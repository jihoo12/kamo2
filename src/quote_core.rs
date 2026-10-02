//! Internal syntax quotation for normalize/recheck without adding parser syntax.
#![allow(dead_code)]
use crate::arena::Key;
use crate::eval::{Engine, Env, Val, ValId};
use crate::face::{Dim, FaceId};
use crate::syntax::{D, Node, Program, Term, TermId};
use crate::{Error, Result};

pub(crate) struct QuotedCore {
    base: usize,
    nodes: Vec<Node>,
    pub(crate) root: TermId,
}
impl QuotedCore {
    pub(crate) fn append(self, program: &mut Program) -> Result<TermId> {
        if program.terms.len() != self.base {
            return Err(Error::plain("quotation destination arena changed"));
        }
        for node in self.nodes {
            program.terms.alloc(node);
        }
        Ok(self.root)
    }
}
struct Quote {
    base: usize,
    nodes: Vec<Node>,
    terms: Vec<u32>,
    dims: Vec<u32>,
    face_work: usize,
}
impl Quote {
    fn face(&mut self, faces: &crate::face::Faces, f: FaceId) -> Result<crate::syntax::F> {
        let dims = &self.dims;
        faces.to_syntax(
            f,
            &|d| match d {
                Dim::Zero => Ok(D::Zero),
                Dim::One => Ok(D::One),
                Dim::Var(v) => dims
                    .iter()
                    .rev()
                    .position(|x| *x == v)
                    .map(D::Bound)
                    .ok_or_else(|| Error::plain("escaped quotation dimension")),
            },
            &mut self.face_work,
        )
    }
    fn alloc(&mut self, term: Term) -> Result<TermId> {
        if self.nodes.len() >= 100_000 {
            return Err(Error::plain("core quotation node budget exhausted"));
        }
        let id = TermId::new(
            self.base
                .checked_add(self.nodes.len())
                .ok_or_else(|| Error::plain("quotation ID overflow"))?,
        );
        self.nodes.push(Node { term, offset: 0 });
        Ok(id)
    }
    fn dim(&self, d: Dim) -> Result<D> {
        match d {
            Dim::Zero => Ok(D::Zero),
            Dim::One => Ok(D::One),
            Dim::Var(v) => self
                .dims
                .iter()
                .rev()
                .position(|x| *x == v)
                .map(D::Bound)
                .ok_or_else(|| Error::plain("escaped quotation dimension")),
        }
    }
}
impl Engine<'_> {
    pub(crate) fn quote_core(
        &mut self,
        value: ValId,
        ty: ValId,
        face: FaceId,
    ) -> Result<QuotedCore> {
        let mut q = Quote {
            base: self.program.terms.len(),
            nodes: vec![],
            terms: vec![],
            dims: vec![],
            face_work: 32_768,
        };
        let root = self.reify(value, Some(ty), face, &mut q, 0)?;
        self.tick()?;
        Ok(QuotedCore {
            base: q.base,
            nodes: q.nodes,
            root,
        })
    }

    fn reify(
        &mut self,
        value: ValId,
        ty: Option<ValId>,
        face: FaceId,
        q: &mut Quote,
        depth: usize,
    ) -> Result<TermId> {
        self.tick()?;
        if depth >= 32 {
            return Err(Error::plain("core quotation depth budget exhausted"));
        }
        let depth = depth + 1;
        if let Some(ty) = ty {
            let ty = self.force(ty, face)?;
            match self.get(ty) {
                Val::Pi(domain, codomain) => {
                    let x = self.variable(domain);
                    let Val::Var(level, _) = self.get(x) else {
                        unreachable!()
                    };
                    q.terms.push(level);
                    let body = self.app(value, x);
                    let body_ty = self.inst(&codomain, x);
                    let body = self.reify(body, Some(body_ty), face, q, depth)?;
                    q.terms.pop();
                    return q.alloc(Term::Lam(body));
                }
                Val::Sigma(domain, codomain) => {
                    let x = self.fst(value);
                    let y = self.snd(value);
                    let yty = self.inst(&codomain, x);
                    let x = self.reify(x, Some(domain), face, q, depth)?;
                    let y = self.reify(y, Some(yty), face, q, depth)?;
                    return q.alloc(Term::Pair(x, y));
                }
                Val::Path(family, _, _) => {
                    let i = self.fresh_dim();
                    q.dims.push(i);
                    let body = self.at(value, Dim::Var(i));
                    let ty = self.inst_dim(&family, Dim::Var(i));
                    let body = self.reify(body, Some(ty), face, q, depth)?;
                    q.dims.pop();
                    return q.alloc(Term::PLam(body));
                }
                Val::Glue(base, branches) => {
                    let g = self.reify(ty, None, face, q, depth)?;
                    let unglued = self.alloc(Val::Unglue(ty, value));
                    let base = self.reify(unglued, Some(base), face, q, depth)?;
                    let mut pieces = vec![];
                    for (f, t, _) in branches {
                        let under = self.faces.and(face, f);
                        if self.faces.inconsistent(under)? {
                            continue;
                        }
                        let f = q.face(&self.faces, f)?;
                        let t = self.reify(value, Some(t), under, q, depth)?;
                        pieces.push((f, t));
                    }
                    return q.alloc(Term::GlueIntro(g, base, pieces));
                }
                _ => {}
            }
        }
        let value = self.force(value, face)?;
        let term = match self.get(value) {
            Val::Var(v, _) => Term::Var(
                q.terms
                    .iter()
                    .rev()
                    .position(|x| *x == v)
                    .ok_or_else(|| Error::plain("escaped quotation term variable"))?,
            ),
            Val::U(l) => Term::U(l),
            Val::Bool => Term::Bool,
            Val::Nat => Term::Nat,
            Val::True => Term::True,
            Val::False => Term::False,
            Val::Zero => Term::Zero,
            Val::Inductive(id) => Term::Inductive(id),
            Val::Constructor(id) => Term::Constructor(id),
            Val::HigherApp {
                constructor,
                parameters,
                arguments,
                dimensions,
            } => {
                let h = self.program.higher_constructor(constructor)?.clone();
                let family = self.program.inductives[h.inductive.index()].clone();
                let pc = parameters.len();
                let mut values = vec![];
                let mut env = self.env(Env::default());
                for (value, entry) in parameters
                    .into_iter()
                    .chain(arguments)
                    .zip(family.parameters.iter().chain(&h.arguments))
                {
                    let ty = self.thunk(entry.ty, env);
                    values.push(self.reify(value, Some(ty), face, q, depth)?);
                    let mut next = self.environment(env);
                    next.terms.push(value);
                    env = self.env(next);
                }
                let arguments = values.split_off(pc);
                Term::HigherApp {
                    constructor,
                    parameters: values,
                    arguments,
                    dimensions: dimensions
                        .into_iter()
                        .map(|d| q.dim(d))
                        .collect::<Result<_>>()?,
                }
            }
            Val::Pi(domain, binder) | Val::Sigma(domain, binder) => {
                let domain_term = self.reify(domain, None, face, q, depth)?;
                let x = self.variable(domain);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                q.terms.push(level);
                let body = self.inst(&binder, x);
                let body = self.reify(body, None, face, q, depth)?;
                q.terms.pop();
                if matches!(self.get(value), Val::Pi(..)) {
                    Term::Pi(domain_term, body)
                } else {
                    Term::Sigma(domain_term, body)
                }
            }
            Val::Path(family, l, r) => {
                let i = self.fresh_dim();
                q.dims.push(i);
                let body = self.inst_dim(&family, Dim::Var(i));
                let body = self.reify(body, None, face, q, depth)?;
                q.dims.pop();
                let lt = self.inst_dim(&family, Dim::Zero);
                let rt = self.inst_dim(&family, Dim::One);
                Term::Path(
                    body,
                    self.reify(l, Some(lt), face, q, depth)?,
                    self.reify(r, Some(rt), face, q, depth)?,
                )
            }
            Val::App(f, a) => {
                let ft = self.neutral_type(f, face)?;
                let ft = self.force(ft, face)?;
                let Val::Pi(dom, _) = self.get(ft) else {
                    return Err(Error::plain("quotation application type"));
                };
                Term::App(
                    self.reify(f, None, face, q, depth)?,
                    self.reify(a, Some(dom), face, q, depth)?,
                )
            }
            Val::Fst(v) => Term::Fst(self.reify(v, None, face, q, depth)?),
            Val::Snd(v) => Term::Snd(self.reify(v, None, face, q, depth)?),
            Val::Suc(v) => {
                let nat = self.alloc(Val::Nat);
                Term::Suc(self.reify(v, Some(nat), face, q, depth)?)
            }
            Val::PApp(p, d) => Term::PApp(self.reify(p, None, face, q, depth)?, q.dim(d)?),
            Val::Unglue(g, v) => Term::Unglue(
                self.reify(g, None, face, q, depth)?,
                self.reify(v, None, face, q, depth)?,
            ),
            Val::System(ty, bs) => {
                let t = self.reify(ty, None, face, q, depth)?;
                let mut pieces = vec![];
                for (f, v) in bs {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    let f = q.face(&self.faces, f)?;
                    pieces.push((f, self.reify(v, Some(ty), under, q, depth)?));
                }
                Term::System(t, pieces)
            }
            Val::Glue(base, bs) => {
                let b = self.reify(base, None, face, q, depth)?;
                let mut pieces = vec![];
                for (f, t, e) in bs {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    let f = q.face(&self.faces, f)?;
                    let ety = self.equiv_type(t, base);
                    pieces.push((
                        f,
                        self.reify(t, None, under, q, depth)?,
                        self.reify(e, Some(ety), under, q, depth)?,
                    ));
                }
                Term::Glue(b, pieces)
            }
            Val::Com(c) => {
                let from = q.dim(c.from)?;
                let to = q.dim(c.to)?;
                let src = self.restrict(c.family, c.dim, c.from);
                let cap = self.reify(c.cap, Some(src), face, q, depth)?;
                // Tube faces live outside the composition dimension binder.
                let faces = c
                    .tubes
                    .iter()
                    .map(|(f, _)| q.face(&self.faces, *f))
                    .collect::<Result<Vec<_>>>()?;
                q.dims.push(c.dim);
                let family = self.reify(c.family, None, face, q, depth)?;
                let mut tubes = vec![];
                for ((f, v), syntax) in c.tubes.into_iter().zip(faces) {
                    let under = self.faces.and(face, f);
                    if self.faces.inconsistent(under)? {
                        continue;
                    }
                    tubes.push((syntax, self.reify(v, Some(c.family), under, q, depth)?));
                }
                q.dims.pop();
                Term::Com {
                    family,
                    from,
                    to,
                    cap,
                    tubes,
                }
            }
            // These neutral eliminators have typed introduction-form payloads.
            // Reify them with the existing type constructors rather than guessing
            // a lambda's domain from its syntax.
            Val::If(p, a, b, c) => {
                let bool_ty = self.alloc(Val::Bool);
                let x = self.variable(bool_ty);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                q.terms.push(level);
                let px = self.app(p, x);
                let body = self.reify(px, None, face, q, depth)?;
                q.terms.pop();
                let pterm = q.alloc(Term::Lam(body))?;
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let at = self.app(p, tv);
                let bt = self.app(p, fv);
                Term::If(
                    pterm,
                    self.reify(a, Some(at), face, q, depth)?,
                    self.reify(b, Some(bt), face, q, depth)?,
                    self.reify(c, Some(bool_ty), face, q, depth)?,
                )
            }
            Val::NatElim(p, z, s, k) => {
                let nat = self.alloc(Val::Nat);
                let x = self.variable(nat);
                let Val::Var(level, _) = self.get(x) else {
                    unreachable!()
                };
                q.terms.push(level);
                let px = self.app(p, x);
                let body = self.reify(px, None, face, q, depth)?;
                let ih = self.variable(px);
                let Val::Var(ihlevel, _) = self.get(ih) else {
                    unreachable!()
                };
                q.terms.push(ihlevel);
                let sx = self.app(s, x);
                let sx = self.app(sx, ih);
                let suc = self.alloc(Val::Suc(x));
                let sty = self.app(p, suc);
                let step = self.reify(sx, Some(sty), face, q, depth)?;
                q.terms.pop();
                q.terms.pop();
                let step = q.alloc(Term::Lam(step))?;
                let step = q.alloc(Term::Lam(step))?;
                let pterm = q.alloc(Term::Lam(body))?;
                let zero = self.alloc(Val::Zero);
                let zty = self.app(p, zero);
                Term::NatElim(
                    pterm,
                    self.reify(z, Some(zty), face, q, depth)?,
                    step,
                    self.reify(k, Some(nat), face, q, depth)?,
                )
            }
            Val::HitElim {
                inductive,
                parameters,
                motive,
                methods,
                indices,
                scrutinee,
            } => {
                let declaration = self.program.inductives[inductive.index()].clone();
                let members = declaration.constructors.higher()?.to_vec();
                let mut parameter_terms = Vec::with_capacity(parameters.len());
                for parameter in parameters.iter().copied() {
                    parameter_terms.push(self.reify(parameter, None, face, q, depth)?);
                }
                let motive_type =
                    self.hit_motive_type(inductive, &parameters, declaration.universe)?;
                let motive_term = self.reify(motive, Some(motive_type), face, q, depth)?;
                let mut method_terms = Vec::with_capacity(methods.len());
                let mut checked_methods = Vec::with_capacity(methods.len());
                for (method, member) in methods.iter().copied().zip(members) {
                    let method_type = match member {
                        crate::hit::ConstructorRef::Point(constructor) => {
                            self.hit_point_method_type(constructor, &parameters, motive, face)?
                        }
                        crate::hit::ConstructorRef::Higher(constructor) => self
                            .hit_higher_method_type(
                                constructor,
                                &parameters,
                                motive,
                                &checked_methods,
                                face,
                            )?,
                    };
                    method_terms.push(self.reify(method, Some(method_type), face, q, depth)?);
                    checked_methods.push(method);
                }
                let mut index_terms = Vec::with_capacity(indices.len());
                for index in indices {
                    index_terms.push(self.reify(index, None, face, q, depth)?);
                }
                Term::HitElim {
                    inductive,
                    parameters: parameter_terms,
                    motive: motive_term,
                    methods: method_terms,
                    indices: index_terms,
                    scrutinee: self.reify(scrutinee, None, face, q, depth)?,
                }
            }
            Val::Elim { .. } => {
                return Err(Error::plain(
                    "core quotation of ordinary eliminators is not implemented",
                ));
            }
            Val::Lam(_) | Val::PLam(_) | Val::Pair(..) | Val::GlueIntro(..) => {
                return Err(Error::plain("core quotation requires introduction type"));
            }
            Val::Sub(..) | Val::Susp(..) => unreachable!("force removes suspensions"),
        };
        q.alloc(term)
    }
}
