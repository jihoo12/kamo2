#[path = "hit_semantic.rs"]
mod hit_semantic;
pub(crate) use hit_semantic::validate as validate_higher;

use crate::arena::Key;
use crate::eval::{Binder, Engine, Env, EnvId, Val, ValId};
use crate::face::{Dim, FaceId};
use crate::hit::ConstructorRef;
use crate::syntax::{Term, TermId};
use crate::{Error, Result};

fn require_hit_member(members: &[ConstructorRef], member: ConstructorRef) -> Result<()> {
    if members.contains(&member) {
        Ok(())
    } else {
        Err(Error::plain("constructor is missing from its HIT family"))
    }
}

#[derive(Clone)]
struct Context {
    env: EnvId,
    types: Vec<ValId>,
    face: FaceId,
}
impl Engine<'_> {
    pub fn check_inductive_declarations(&mut self) -> Result<()> {
        for family in self.program.inductives.clone() {
            if family.constructors.is_higher() {
                continue;
            }
            let env = self.env(Env::default());
            let mut context = Context {
                env,
                types: vec![],
                face: self.faces.top(),
            };
            for entry in &family.parameters {
                self.sort(entry.ty, &context)?;
                let ty = self.thunk(entry.ty, context.env);
                let (next, _) = self.extend(&context, ty);
                context = next;
            }
            for entry in &family.indices {
                self.sort(entry.ty, &context)?;
                let ty = self.thunk(entry.ty, context.env);
                let (next, _) = self.extend(&context, ty);
                context = next;
            }
            for constructor_id in family.constructors.ordinary()? {
                let constructor = self.program.constructors[constructor_id.index()].clone();
                let env = self.env(Env::default());
                let mut constructor_context = Context {
                    env,
                    types: vec![],
                    face: self.faces.top(),
                };
                let mut parameter_values = Vec::new();
                for entry in &family.parameters {
                    let ty = self.thunk(entry.ty, constructor_context.env);
                    let (next, value) = self.extend(&constructor_context, ty);
                    constructor_context = next;
                    parameter_values.push(value);
                }
                for entry in &constructor.arguments {
                    let level = self.sort(entry.ty, &constructor_context)?;
                    if level > family.universe {
                        return Err(self.error(
                            entry.ty,
                            format!(
                                "constructor field '{}' lives in U {level}, above inductive universe U {}",
                                entry.name, family.universe
                            ),
                        ));
                    }
                    let ty = self.thunk(entry.ty, constructor_context.env);
                    let (next, _) = self.extend(&constructor_context, ty);
                    constructor_context = next;
                }
                let mut index_environment = Env::default();
                index_environment.terms.extend_from_slice(&parameter_values);
                let mut index_environment = self.env(index_environment);
                for (entry, result) in family.indices.iter().zip(&constructor.result_indices) {
                    let domain = self.thunk(entry.ty, index_environment);
                    self.check(*result, domain, &constructor_context)?;
                    let value = self.thunk(*result, constructor_context.env);
                    let mut next = self.environment(index_environment);
                    next.terms.push(value);
                    index_environment = self.env(next);
                }
            }
        }
        Ok(())
    }

    pub fn check_declaration(&mut self, index: usize) -> Result<()> {
        let decl = &self.program.decls[index];
        {
            if std::env::var_os("KAMO_TRACE_CHECK").is_some() {
                eprintln!("checking {} ({} steps)", decl.name, self.steps);
            }
            let env = self.env(Env::default());
            let face = self.faces.top();
            let ctx = Context {
                env,
                types: vec![],
                face,
            };
            self.sort(decl.ty, &ctx).map_err(|mut e| {
                e.message = format!("checking type of {}: {}", decl.name, e.message);
                e
            })?;
            let ty = self.thunk(decl.ty, env);
            self.check(decl.body, ty, &ctx).map_err(|mut e| {
                e.message = format!("checking {}: {}", decl.name, e.message);
                e
            })?;
        }
        self.tick()?;
        Ok(())
    }
    fn error(&self, t: TermId, message: impl Into<String>) -> Error {
        Error::at(self.program.terms.get(t).offset, message)
    }
    fn extend(&mut self, ctx: &Context, ty: ValId) -> (Context, ValId) {
        let x = self.variable(ty);
        let mut env = self.environment(ctx.env);
        env.terms.push(x);
        let mut c = ctx.clone();
        c.env = self.env(env);
        c.types.push(ty);
        (c, x)
    }
    fn interval(&mut self, ctx: &Context) -> (Context, u32) {
        let i = self.fresh_dim();
        let mut env = self.environment(ctx.env);
        env.dims.push(Dim::Var(i));
        let mut c = ctx.clone();
        c.env = self.env(env);
        (c, i)
    }
    fn interval_at(&mut self, ctx: &Context, d: Dim) -> Context {
        let mut env = self.environment(ctx.env);
        env.dims.push(d);
        Context {
            env: self.env(env),
            ..ctx.clone()
        }
    }
    fn sort(&mut self, t: TermId, ctx: &Context) -> Result<u32> {
        let ty = self.infer(t, ctx)?;
        let ty = self.force(ty, ctx.face)?;
        if let Val::U(l) = self.get(ty) {
            Ok(l)
        } else {
            Err(self.error(t, "expected a type (an inhabitant of a universe)"))
        }
    }
    fn check(&mut self, t: TermId, ty: ValId, ctx: &Context) -> Result<()> {
        self.check_inner(t, ty, ctx).map_err(|mut e| {
            if e.offset.is_none() {
                e.offset = Some(self.program.terms.get(t).offset);
            }
            e
        })
    }
    fn check_inner(&mut self, t: TermId, ty: ValId, ctx: &Context) -> Result<()> {
        self.tick()?;
        if self.faces.inconsistent(ctx.face)? {
            return Ok(());
        }
        // Equality and checking are local on covers; no branch choice is global.
        let clauses = self.faces.clauses(ctx.face)?;
        if clauses.len() > 1 {
            for face in clauses {
                self.check(
                    t,
                    ty,
                    &Context {
                        face,
                        ..ctx.clone()
                    },
                )?;
            }
            return Ok(());
        }
        let ty = self.force(ty, ctx.face)?;
        match (self.program.terms.get(t).term.clone(), self.get(ty)) {
            (Term::Lam(body), Val::Pi(a, b)) => {
                let (ctx, x) = self.extend(ctx, a);
                let b = self.inst(&b, x);
                self.check(body, b, &ctx)
            }
            (Term::Pair(a, b), Val::Sigma(first, second)) => {
                self.check(a, first, ctx)?;
                let a = self.thunk(a, ctx.env);
                let second = self.inst(&second, a);
                self.check(b, second, ctx)
            }
            (Term::PLam(body), Val::Path(family, left, right)) => {
                let (inner, i) = self.interval(ctx);
                let a = self.inst_dim(&family, Dim::Var(i));
                self.check(body, a, &inner)?;
                for (d, endpoint) in [(Dim::Zero, left), (Dim::One, right)] {
                    let at = self.interval_at(ctx, d);
                    let body = self.thunk(body, at.env);
                    let a = self.inst_dim(&family, d);
                    if !self.conv(body, endpoint, Some(a), ctx.face)? {
                        return Err(
                            self.error(t, "path endpoint does not match its declared boundary")
                        );
                    }
                }
                Ok(())
            }
            _ => {
                let got = self.infer(t, ctx)?;
                if self.compatible(got, ty, ctx.face)? {
                    Ok(())
                } else {
                    Err(self.error(t, "type mismatch"))
                }
            }
        }
    }
    fn compatible(&mut self, got: ValId, expected: ValId, face: FaceId) -> Result<bool> {
        if self.conv(got, expected, None, face)? {
            return Ok(true);
        }
        let got = self.force(got, face)?;
        let expected = self.force(expected, face)?;
        match (self.get(got), self.get(expected)) {
            (Val::U(i), Val::U(j)) => Ok(i <= j),
            _ => Ok(false),
        }
    }
    fn infer(&mut self, t: TermId, ctx: &Context) -> Result<ValId> {
        self.tick()?;
        let ty = match self.program.terms.get(t).term.clone() {
            Term::Var(i) => {
                return i
                    .checked_add(1)
                    .and_then(|n| ctx.types.len().checked_sub(n))
                    .and_then(|j| ctx.types.get(j))
                    .copied()
                    .ok_or_else(|| self.error(t, "escaped term variable"));
            }
            Term::Global(i) => {
                let e = self.env(Env::default());
                return Ok(self.thunk(self.program.decls[i].ty, e));
            }
            Term::U(l) => Val::U(
                l.checked_add(1)
                    .ok_or_else(|| self.error(t, "universe level overflow"))?,
            ),
            Term::Bool | Term::Nat => Val::U(0),
            Term::Inductive(id) => return Ok(self.inductive_type(id)),
            Term::Constructor(id) => return Ok(self.constructor_type(id)),
            Term::HigherApp {
                constructor,
                parameters,
                arguments,
                dimensions,
            } => {
                let h = self.program.higher_constructor(constructor)?.clone();
                let family = self
                    .program
                    .inductives
                    .get(h.inductive.index())
                    .ok_or_else(|| Error::plain("missing higher owner"))?
                    .clone();
                if parameters.len() != family.parameters.len()
                    || arguments.len() != h.arguments.len()
                    || dimensions.len() != 1
                {
                    return Err(self.error(t, "higher application arity mismatch"));
                }
                let dimension_count = self.environment(ctx.env).dims.len();
                for d in &dimensions {
                    if matches!(d, crate::syntax::D::Bound(i) if *i >= dimension_count) {
                        return Err(self.error(t, "escaped higher application dimension"));
                    }
                }
                let mut env = self.env(Env::default());
                let mut values = Vec::new();
                for (argument, entry) in parameters
                    .iter()
                    .chain(&arguments)
                    .zip(family.parameters.iter().chain(&h.arguments))
                {
                    if argument.index() >= self.program.terms.len() {
                        return Err(self.error(t, "invalid higher argument term ID"));
                    }
                    let ty = self.thunk(entry.ty, env);
                    self.check(*argument, ty, ctx)?;
                    let value = self.thunk(*argument, ctx.env);
                    values.push(value);
                    let mut next = self.environment(env);
                    next.terms.push(value);
                    env = self.env(next);
                }
                let ds = dimensions
                    .into_iter()
                    .map(|d| self.dim(d, ctx.env))
                    .collect::<Vec<_>>();
                return self.higher_result(
                    constructor,
                    &values[..parameters.len()],
                    &values[parameters.len()..],
                    &ds,
                );
            }
            Term::Elim {
                inductive,
                parameters,
                motive,
                methods,
                indices,
                scrutinee,
            } => {
                let declaration = self.program.inductives[inductive.index()].clone();
                declaration.constructors.ordinary()?;
                if parameters.len() != declaration.parameters.len() {
                    return Err(self.error(t, "wrong number of inductive parameters"));
                }
                if indices.len() != declaration.indices.len() {
                    return Err(self.error(t, "wrong number of inductive indices"));
                }
                if methods.len() != declaration.constructors.ordinary()?.len() {
                    return Err(self.error(t, "wrong number of eliminator methods"));
                }

                let mut family = self.alloc(Val::Inductive(inductive));
                let mut parameter_values = Vec::with_capacity(parameters.len());
                for parameter in parameters {
                    let family_ty = self.neutral_type(family, ctx.face)?;
                    let family_ty = self.force(family_ty, ctx.face)?;
                    let Val::Pi(domain, _) = self.get(family_ty) else {
                        return Err(self.error(t, "malformed inductive parameter telescope"));
                    };
                    self.check(parameter, domain, ctx)?;
                    let parameter = self.thunk(parameter, ctx.env);
                    parameter_values.push(parameter);
                    family = self.app(family, parameter);
                }

                let mut index_values = Vec::with_capacity(indices.len());
                for index in indices {
                    let family_ty = self.neutral_type(family, ctx.face)?;
                    let family_ty = self.force(family_ty, ctx.face)?;
                    let Val::Pi(domain, _) = self.get(family_ty) else {
                        return Err(self.error(t, "malformed inductive index telescope"));
                    };
                    self.check(index, domain, ctx)?;
                    let index = self.thunk(index, ctx.env);
                    index_values.push(index);
                    family = self.app(family, index);
                }
                self.check(scrutinee, family, ctx)?;

                let motive_type =
                    self.generic_motive_type(inductive, &parameter_values, declaration.universe)?;
                self.check(motive, motive_type, ctx)?;
                let motive_value = self.thunk(motive, ctx.env);

                for (method, constructor) in methods
                    .into_iter()
                    .zip(declaration.constructors.ordinary()?.iter().copied())
                {
                    let method_type = self.generic_method_type(
                        constructor,
                        &parameter_values,
                        motive_value,
                        ctx.face,
                    )?;
                    self.check(method, method_type, ctx)?;
                }

                let mut result = motive_value;
                for index in index_values {
                    result = self.app(result, index);
                }
                let scrutinee = self.thunk(scrutinee, ctx.env);
                return Ok(self.app(result, scrutinee));
            }
            Term::HitElim {
                inductive,
                parameters,
                motive,
                methods,
                indices,
                scrutinee,
            } => {
                let declaration = self.program.inductives[inductive.index()].clone();
                let members = declaration.constructors.higher()?.to_vec();
                if parameters.len() != declaration.parameters.len() {
                    return Err(self.error(t, "wrong number of HIT parameters"));
                }
                if indices.len() != declaration.indices.len() {
                    return Err(self.error(t, "wrong number of HIT indices"));
                }
                if methods.len() != members.len() {
                    return Err(self.error(t, "wrong number of HIT eliminator methods"));
                }

                let mut family = self.alloc(Val::Inductive(inductive));
                let mut parameter_values = Vec::with_capacity(parameters.len());
                for parameter in parameters {
                    let family_ty = self.neutral_type(family, ctx.face)?;
                    let family_ty = self.force(family_ty, ctx.face)?;
                    let Val::Pi(domain, _) = self.get(family_ty) else {
                        return Err(self.error(t, "malformed HIT parameter telescope"));
                    };
                    self.check(parameter, domain, ctx)?;
                    let parameter = self.thunk(parameter, ctx.env);
                    parameter_values.push(parameter);
                    family = self.app(family, parameter);
                }

                let mut index_values = Vec::with_capacity(indices.len());
                for index in indices {
                    let family_ty = self.neutral_type(family, ctx.face)?;
                    let family_ty = self.force(family_ty, ctx.face)?;
                    let Val::Pi(domain, _) = self.get(family_ty) else {
                        return Err(self.error(t, "malformed HIT index telescope"));
                    };
                    self.check(index, domain, ctx)?;
                    let index = self.thunk(index, ctx.env);
                    index_values.push(index);
                    family = self.app(family, index);
                }
                self.check(scrutinee, family, ctx)?;

                let motive_type =
                    self.hit_motive_type(inductive, &parameter_values, declaration.universe)?;
                self.check(motive, motive_type, ctx)?;
                let motive_value = self.thunk(motive, ctx.env);

                let method_terms = methods.clone();
                let mut checked_methods = Vec::with_capacity(method_terms.len());
                for (method, member) in method_terms.into_iter().zip(members) {
                    let method_type = match member {
                        ConstructorRef::Point(constructor) => self.hit_point_method_type(
                            constructor,
                            &parameter_values,
                            motive_value,
                            ctx.face,
                        )?,
                        ConstructorRef::Higher(constructor) => self.hit_higher_method_type(
                            constructor,
                            &parameter_values,
                            motive_value,
                            &checked_methods,
                            ctx.face,
                        )?,
                    };
                    self.check(method, method_type, ctx)?;
                    checked_methods.push(self.thunk(method, ctx.env));
                }

                let mut result = motive_value;
                for index in index_values {
                    result = self.app(result, index);
                }
                let scrutinee = self.thunk(scrutinee, ctx.env);
                return Ok(self.app(result, scrutinee));
            }
            Term::True | Term::False => Val::Bool,
            Term::Zero => Val::Nat,
            Term::Suc(n) => {
                let nat = self.alloc(Val::Nat);
                self.check(n, nat, ctx)?;
                Val::Nat
            }
            Term::Pi(a, b) | Term::Sigma(a, b) => {
                let l = self.sort(a, ctx)?;
                let a = self.thunk(a, ctx.env);
                let (inner, _) = self.extend(ctx, a);
                let m = self.sort(b, &inner)?;
                Val::U(l.max(m))
            }
            Term::Ann(body, ty) => {
                self.sort(ty, ctx)?;
                let ty = self.thunk(ty, ctx.env);
                self.check(body, ty, ctx)?;
                return Ok(ty);
            }
            Term::App(f, a) => {
                let ty = self.infer(f, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Pi(dom, cod) = self.get(ty) {
                    self.check(a, dom, ctx)?;
                    let a = self.thunk(a, ctx.env);
                    return Ok(self.inst(&cod, a));
                }
                return Err(self.error(t, "application expects a dependent function"));
            }
            Term::Fst(p) | Term::Snd(p) => {
                let ty = self.infer(p, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Sigma(a, b) = self.get(ty) {
                    if matches!(self.program.terms.get(t).term, Term::Fst(_)) {
                        return Ok(a);
                    }
                    let p = self.thunk(p, ctx.env);
                    let a = self.fst(p);
                    return Ok(self.inst(&b, a));
                }
                return Err(self.error(t, "projection expects a dependent pair"));
            }
            Term::If(p, a, b, c) => {
                let bool_ty = self.alloc(Val::Bool);
                self.check(c, bool_ty, ctx)?;
                self.check_motive(p, bool_ty, ctx)?;
                let p = self.thunk(p, ctx.env);
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let ta = self.app(p, tv);
                let tb = self.app(p, fv);
                self.check(a, ta, ctx)?;
                self.check(b, tb, ctx)?;
                let c = self.thunk(c, ctx.env);
                return Ok(self.app(p, c));
            }
            Term::NatElim(p, z, s, n) => {
                let nat = self.alloc(Val::Nat);
                self.check(n, nat, ctx)?;
                self.check_motive(p, nat, ctx)?;
                let p = self.thunk(p, ctx.env);
                let zero = self.alloc(Val::Zero);
                let base = self.app(p, zero);
                self.check(z, base, ctx)?;
                let x = self.fresh_term();
                let xv = self.alloc(Val::Var(x, Some(nat)));
                let px = self.app(p, xv);
                let sx = self.alloc(Val::Suc(xv));
                let result = self.app(p, sx);
                let ih = self.fresh_term();
                let step = self.alloc(Val::Pi(
                    px,
                    Binder {
                        var: ih,
                        body: result,
                    },
                ));
                let step = self.alloc(Val::Pi(nat, Binder { var: x, body: step }));
                self.check(s, step, ctx)?;
                let n = self.thunk(n, ctx.env);
                return Ok(self.app(p, n));
            }
            Term::Path(a, l, r) => {
                let (inner, _) = self.interval(ctx);
                let level = self.sort(a, &inner)?;
                for (d, v) in [(Dim::Zero, l), (Dim::One, r)] {
                    let at = self.interval_at(ctx, d);
                    let a = self.thunk(a, at.env);
                    self.check(v, a, ctx)?;
                }
                Val::U(level)
            }
            Term::PApp(p, d) => {
                let ty = self.infer(p, ctx)?;
                let ty = self.force(ty, ctx.face)?;
                if let Val::Path(b, _, _) = self.get(ty) {
                    return Ok(self.inst_dim(&b, self.dim(d, ctx.env)));
                }
                return Err(self.error(t, "'at' expects a path"));
            }
            Term::Com {
                family,
                from,
                to,
                cap,
                tubes,
            } => {
                let (inner, _) = self.interval(ctx);
                self.sort(family, &inner)?;
                let from = self.dim(from, ctx.env);
                let to = self.dim(to, ctx.env);
                let source = self.interval_at(ctx, from);
                let source_ty = self.thunk(family, source.env);
                self.check(cap, source_ty, ctx)?;
                let cap = self.thunk(cap, ctx.env);
                let mut previous = vec![];
                for (f, tube) in tubes {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    let branch = Context {
                        face: under,
                        ..inner.clone()
                    };
                    let ty = self.thunk(family, inner.env);
                    self.check(tube, ty, &branch)?;
                    let start = self.thunk(tube, source.env);
                    if !self.conv(start, cap, Some(source_ty), under)? {
                        return Err(self.error(
                            tube,
                            "composition tube disagrees with its cap at the source",
                        ));
                    }
                    let v = self.thunk(tube, inner.env);
                    for &(old_face, old_v) in &previous {
                        let overlap = self.faces.and(under, old_face);
                        if !self.conv(v, old_v, Some(ty), overlap)? {
                            return Err(
                                self.error(tube, "composition tubes disagree on an overlap")
                            );
                        }
                    }
                    previous.push((f, v));
                }
                let target = self.interval_at(ctx, to);
                return Ok(self.thunk(family, target.env));
            }
            Term::System(a, branches) => {
                self.sort(a, ctx)?;
                let a = self.thunk(a, ctx.env);
                let mut cover = self.faces.bot();
                let mut previous = vec![];
                for (f, body) in branches {
                    let f = self.face(&f, ctx.env);
                    cover = self.faces.or(cover, f);
                    let under = self.faces.and(ctx.face, f);
                    self.check(
                        body,
                        a,
                        &Context {
                            face: under,
                            ..ctx.clone()
                        },
                    )?;
                    let v = self.thunk(body, ctx.env);
                    for &(old_face, old_v) in &previous {
                        let overlap = self.faces.and(under, old_face);
                        if !self.conv(v, old_v, Some(a), overlap)? {
                            return Err(self.error(body, "system branches disagree on an overlap"));
                        }
                    }
                    previous.push((f, v));
                }
                if !self.faces.entails(ctx.face, cover)? {
                    return Err(self.error(t, "system faces do not cover the current face context"));
                }
                return Ok(a);
            }
            Term::Glue(base, branches) => {
                let level = self.sort(base, ctx)?;
                let base = self.thunk(base, ctx.env);
                let universe = self.alloc(Val::U(level));
                let mut previous = vec![];
                for (f, a, e) in branches {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    let branch = Context {
                        face: under,
                        ..ctx.clone()
                    };
                    self.check(a, universe, &branch)?;
                    let a = self.thunk(a, ctx.env);
                    let eqty = self.equiv_type(a, base);
                    self.check(e, eqty, &branch)?;
                    let e = self.thunk(e, ctx.env);
                    for &(g, b, q) in &previous {
                        let overlap = self.faces.and(under, g);
                        if !self.conv(a, b, None, overlap)?
                            || !self.conv(e, q, Some(eqty), overlap)?
                        {
                            return Err(self.error(t, "Glue data disagree on an overlap"));
                        }
                    }
                    previous.push((f, a, e));
                }
                Val::U(level)
            }
            Term::Unglue(g, v) => {
                self.sort(g, ctx)?;
                let g = self.thunk(g, ctx.env);
                let raw = self.force_glue(g, ctx.face)?;
                if let Val::Glue(base, _) = self.get(raw) {
                    self.check(v, g, ctx)?;
                    return Ok(base);
                }
                return Err(self.error(t, "unglue requires an explicit Glue type"));
            }
            Term::GlueIntro(g, base, branches) => {
                self.sort(g, ctx)?;
                let g = self.thunk(g, ctx.env);
                let raw = self.force_glue(g, ctx.face)?;
                let Val::Glue(base_ty, data) = self.get(raw) else {
                    return Err(self.error(t, "glue requires an explicit Glue type"));
                };
                self.check(base, base_ty, ctx)?;
                let base = self.thunk(base, ctx.env);
                let mut domain = self.faces.bot();
                for (f, _, _) in &data {
                    domain = self.faces.or(domain, *f);
                }
                let mut cover = self.faces.bot();
                let mut tops = vec![];
                for (f, body) in branches {
                    let f = self.face(&f, ctx.env);
                    let under = self.faces.and(ctx.face, f);
                    if !self.faces.entails(under, domain)? {
                        return Err(
                            self.error(body, "glue element face exceeds the Glue type's domain")
                        );
                    }
                    cover = self.faces.or(cover, f);
                    let v = self.thunk(body, ctx.env);
                    for &(h, a, e) in &data {
                        let overlap = self.faces.and(under, h);
                        self.check(
                            body,
                            a,
                            &Context {
                                face: overlap,
                                ..ctx.clone()
                            },
                        )?;
                        let fun = self.fst(e);
                        let image = self.app(fun, v);
                        if !self.conv(image, base, Some(base_ty), overlap)? {
                            return Err(
                                self.error(body, "glue element image disagrees with its base")
                            );
                        }
                        for &(old_face, old_v) in &tops {
                            let both = self.faces.and(overlap, old_face);
                            if !self.conv(v, old_v, Some(a), both)? {
                                return Err(
                                    self.error(body, "glue elements disagree on an overlap")
                                );
                            }
                        }
                    }
                    tops.push((f, v));
                }
                let required = self.faces.and(ctx.face, domain);
                if !self.faces.entails(required, cover)? {
                    return Err(self.error(t, "glue elements do not cover the Glue type's domain"));
                }
                return Ok(g);
            }
            Term::Lam(_) | Term::Pair(_, _) | Term::PLam(_) => {
                return Err(self.error(t, "cannot infer an introduction form; add (ann term type)"));
            }
        };
        Ok(self.alloc(ty))
    }
    pub(crate) fn generic_method_type(
        &mut self,
        constructor_id: crate::syntax::ConstructorId,
        parameters: &[ValId],
        motive: ValId,
        face: FaceId,
    ) -> Result<ValId> {
        let constructor = self.program.constructors[constructor_id.index()].clone();
        self.program.inductives[constructor.inductive.index()]
            .constructors
            .ordinary()?;
        let mut env = Env::default();
        env.terms.extend_from_slice(parameters);
        let env = self.env(env);
        self.bind_generic_method_arguments(&constructor, parameters, motive, face, 0, env)
    }

    fn bind_generic_method_arguments(
        &mut self,
        constructor: &crate::syntax::ConstructorDecl,
        parameters: &[ValId],
        motive: ValId,
        face: FaceId,
        index: usize,
        env: EnvId,
    ) -> Result<ValId> {
        let parameter_count = parameters.len();
        if index == constructor.arguments.len() {
            let values = self.environment(env).terms;
            let mut constructor_value = self.alloc(Val::Constructor(constructor.id));
            for parameter in parameters {
                constructor_value = self.app(constructor_value, *parameter);
            }
            for argument in values.iter().skip(parameter_count) {
                constructor_value = self.app(constructor_value, *argument);
            }
            let mut result = motive;
            for result_index in &constructor.result_indices {
                let value = self.thunk(*result_index, env);
                result = self.app(result, value);
            }
            return Ok(self.app(result, constructor_value));
        }

        let domain = self.thunk(constructor.arguments[index].ty, env);
        let var = self.fresh_term();
        let value = self.alloc(Val::Var(var, Some(domain)));
        let mut next = self.environment(env);
        next.terms.push(value);
        let next = self.env(next);

        let mut body = self.bind_generic_method_arguments(
            constructor,
            parameters,
            motive,
            face,
            index + 1,
            next,
        )?;

        if constructor.recursive_arguments.contains(&index) {
            let Some((recursive_family, application)) = self.inductive_application(domain, face)?
            else {
                return Err(Error::plain(
                    "recursive constructor argument is not an inductive family",
                ));
            };
            if recursive_family != constructor.inductive || application.len() < parameter_count {
                return Err(Error::plain(
                    "recursive constructor argument has the wrong inductive family",
                ));
            }
            let mut ih_type = motive;
            for recursive_index in application.iter().skip(parameter_count) {
                ih_type = self.app(ih_type, *recursive_index);
            }
            ih_type = self.app(ih_type, value);
            let ih = self.fresh_term();
            body = self.alloc(Val::Pi(ih_type, Binder { var: ih, body }));
        }

        Ok(self.alloc(Val::Pi(domain, Binder { var, body })))
    }

    pub(crate) fn hit_point_method_type(
        &mut self,
        constructor_id: crate::syntax::ConstructorId,
        parameters: &[ValId],
        motive: ValId,
        face: FaceId,
    ) -> Result<ValId> {
        let constructor = self.program.constructors[constructor_id.index()].clone();
        let family = &self.program.inductives[constructor.inductive.index()];
        require_hit_member(
            family.constructors.higher()?,
            ConstructorRef::Point(constructor_id),
        )?;
        let mut env = Env::default();
        env.terms.extend_from_slice(parameters);
        let env = self.env(env);
        self.bind_generic_method_arguments(&constructor, parameters, motive, face, 0, env)
    }

    pub(crate) fn hit_higher_method_type(
        &mut self,
        constructor_id: crate::hit::HigherConstructorId,
        parameters: &[ValId],
        motive: ValId,
        checked_methods: &[ValId],
        face: FaceId,
    ) -> Result<ValId> {
        let constructor = self.program.higher_constructor(constructor_id)?.clone();
        let family = self.program.inductives[constructor.inductive.index()].clone();
        require_hit_member(
            family.constructors.higher()?,
            ConstructorRef::Higher(constructor_id),
        )?;
        if constructor.dimensions.len() != 1 {
            return Err(Error::plain(
                "Slice D HIT elimination supports exactly one dimension",
            ));
        }
        let mut env = Env::default();
        env.terms.extend_from_slice(parameters);
        let env = self.env(env);
        self.bind_hit_higher_method_arguments(&constructor, motive, checked_methods, face, 0, env)
    }

    fn bind_hit_higher_method_arguments(
        &mut self,
        constructor: &crate::hit::HigherConstructorDecl,
        motive: ValId,
        checked_methods: &[ValId],
        face: FaceId,
        index: usize,
        env: EnvId,
    ) -> Result<ValId> {
        if index == constructor.arguments.len() {
            let values = self.environment(env).terms;
            let parameter_count = self.program.inductives[constructor.inductive.index()]
                .parameters
                .len();
            let parameters = values[..parameter_count].to_vec();
            let arguments = values[parameter_count..].to_vec();
            let dimension = self.fresh_dim();
            let mut body_env = self.environment(env);
            body_env.dims.push(Dim::Var(dimension));
            let body_env = self.env(body_env);

            let indices = constructor
                .result_indices
                .iter()
                .map(|index| self.thunk(*index, body_env))
                .collect::<Vec<_>>();
            let higher = self.alloc(Val::HigherApp {
                constructor: constructor.id,
                parameters: parameters.clone(),
                arguments,
                dimensions: vec![Dim::Var(dimension)],
            });

            let mut family = motive;
            for index in &indices {
                family = self.app(family, *index);
            }
            family = self.app(family, higher);

            let eliminator = self.alloc(Val::HitElim {
                inductive: constructor.inductive,
                parameters: parameters.clone(),
                motive,
                methods: checked_methods.to_vec(),
                indices,
                scrutinee: higher,
            });
            let left = self.restrict(eliminator, dimension, Dim::Zero);
            let left = self.force(left, face)?;
            let right = self.restrict(eliminator, dimension, Dim::One);
            let right = self.force(right, face)?;
            return Ok(self.alloc(Val::Path(
                Binder {
                    var: dimension,
                    body: family,
                },
                left,
                right,
            )));
        }

        let domain = self.thunk(constructor.arguments[index].ty, env);
        let var = self.fresh_term();
        let value = self.alloc(Val::Var(var, Some(domain)));
        let mut next = self.environment(env);
        next.terms.push(value);
        let next = self.env(next);
        let body = self.bind_hit_higher_method_arguments(
            constructor,
            motive,
            checked_methods,
            face,
            index + 1,
            next,
        )?;
        Ok(self.alloc(Val::Pi(domain, Binder { var, body })))
    }

    pub(crate) fn hit_motive_type(
        &mut self,
        inductive: crate::syntax::InductiveId,
        parameters: &[ValId],
        universe: u32,
    ) -> Result<ValId> {
        let declaration = self.program.inductives[inductive.index()].clone();
        declaration.constructors.higher()?;
        let mut env = Env::default();
        env.terms.extend_from_slice(parameters);
        let env = self.env(env);
        Ok(self.bind_generic_motive_indices(
            inductive,
            parameters,
            &declaration.indices,
            0,
            env,
            universe,
        ))
    }

    pub(crate) fn generic_motive_type(
        &mut self,
        inductive: crate::syntax::InductiveId,
        parameters: &[ValId],
        universe: u32,
    ) -> Result<ValId> {
        let declaration = self.program.inductives[inductive.index()].clone();
        declaration.constructors.ordinary()?;
        let mut env = Env::default();
        env.terms.extend_from_slice(parameters);
        let env = self.env(env);
        Ok(self.bind_generic_motive_indices(
            inductive,
            parameters,
            &declaration.indices,
            0,
            env,
            universe,
        ))
    }

    fn bind_generic_motive_indices(
        &mut self,
        inductive: crate::syntax::InductiveId,
        parameters: &[ValId],
        indices: &[crate::syntax::TelescopeEntry],
        index: usize,
        env: EnvId,
        universe: u32,
    ) -> ValId {
        if index == indices.len() {
            let values = self.environment(env).terms;
            let mut family = self.alloc(Val::Inductive(inductive));
            for parameter in parameters {
                family = self.app(family, *parameter);
            }
            for value in values.iter().skip(parameters.len()) {
                family = self.app(family, *value);
            }
            let scrutinee = self.fresh_term();
            let codomain = self.alloc(Val::U(universe));
            return self.alloc(Val::Pi(
                family,
                Binder {
                    var: scrutinee,
                    body: codomain,
                },
            ));
        }
        let domain = self.thunk(indices[index].ty, env);
        let var = self.fresh_term();
        let value = self.alloc(Val::Var(var, Some(domain)));
        let mut next = self.environment(env);
        next.terms.push(value);
        let next = self.env(next);
        let body = self.bind_generic_motive_indices(
            inductive,
            parameters,
            indices,
            index + 1,
            next,
            universe,
        );
        self.alloc(Val::Pi(domain, Binder { var, body }))
    }

    fn check_motive(&mut self, p: TermId, domain: ValId, ctx: &Context) -> Result<()> {
        // A syntactic lambda is permitted here without a universe annotation.
        if let Term::Lam(body) = self.program.terms.get(p).term {
            let (inner, _) = self.extend(ctx, domain);
            self.sort(body, &inner)?;
            return Ok(());
        }
        let ty = self.infer(p, ctx)?;
        let ty = self.force(ty, ctx.face)?;
        if let Val::Pi(a, b) = self.get(ty)
            && self.conv(a, domain, None, ctx.face)?
        {
            let x = self.variable(a);
            let b = self.inst(&b, x);
            let b = self.force(b, ctx.face)?;
            if matches!(self.get(b), Val::U(_)) {
                return Ok(());
            }
        }
        Err(self.error(
            p,
            "eliminator motive must map its argument type to a universe",
        ))
    }
    /// Type-directed eta equality; term identities are only compared in one face context.
    pub fn conv(&mut self, a: ValId, b: ValId, ty: Option<ValId>, face: FaceId) -> Result<bool> {
        self.tick()?;
        if self.faces.inconsistent(face)? {
            return Ok(true);
        }
        if a == b {
            return Ok(true);
        }
        if self.same(a, b, face, 128)? {
            return Ok(true);
        }
        let clauses = self.faces.clauses(face)?;
        if clauses.len() > 1 {
            for f in clauses {
                if !self.conv(a, b, ty, f)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if let Some(ty) = ty {
            let ty = self.force(ty, face)?;
            match self.get(ty) {
                Val::Pi(dom, cod) => {
                    let x = self.variable(dom);
                    let ax = self.app(a, x);
                    let bx = self.app(b, x);
                    let cod = self.inst(&cod, x);
                    return self.conv(ax, bx, Some(cod), face);
                }
                Val::Sigma(dom, cod) => {
                    let ax = self.fst(a);
                    let bx = self.fst(b);
                    if !self.conv(ax, bx, Some(dom), face)? {
                        return Ok(false);
                    }
                    let cod = self.inst(&cod, ax);
                    let ay = self.snd(a);
                    let by = self.snd(b);
                    return self.conv(ay, by, Some(cod), face);
                }
                Val::Path(family, _, _) => {
                    let i = self.fresh_dim();
                    let d = Dim::Var(i);
                    let ax = self.at(a, d);
                    let bx = self.at(b, d);
                    let cod = self.inst_dim(&family, d);
                    return self.conv(ax, bx, Some(cod), face);
                }
                Val::Glue(base, branches) => {
                    let ax = self.alloc(Val::Unglue(ty, a));
                    let bx = self.alloc(Val::Unglue(ty, b));
                    if !self.conv(ax, bx, Some(base), face)? {
                        return Ok(false);
                    }
                    for (f, t, _) in branches {
                        let under = self.faces.and(face, f);
                        if !self.conv(a, b, Some(t), under)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                _ => {}
            }
        }
        let a = self.force(a, face)?;
        let b = self.force(b, face)?;
        if a == b {
            return Ok(true);
        }
        if let Val::System(_, branches) = self.get(a) {
            for (f, v) in branches {
                let under = self.faces.and(face, f);
                if !self.conv(v, b, ty, under)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if let Val::System(_, branches) = self.get(b) {
            for (f, v) in branches {
                let under = self.faces.and(face, f);
                if !self.conv(a, v, ty, under)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        match (self.get(a), self.get(b)) {
            (Val::U(a), Val::U(b)) => Ok(a == b),
            (Val::Inductive(a), Val::Inductive(b)) => Ok(a == b),
            (Val::Constructor(a), Val::Constructor(b)) => Ok(a == b),
            (Val::HigherApp { .. }, Val::HigherApp { .. }) => self.higher_congruent(a, b, face),
            (Val::Bool, Val::Bool)
            | (Val::Nat, Val::Nat)
            | (Val::True, Val::True)
            | (Val::False, Val::False)
            | (Val::Zero, Val::Zero) => Ok(true),
            (Val::Var(a, _), Val::Var(b, _)) => Ok(a == b),
            (Val::Pi(a, x), Val::Pi(b, y)) | (Val::Sigma(a, x), Val::Sigma(b, y)) => {
                if !self.conv(a, b, None, face)? {
                    return Ok(false);
                }
                let v = self.variable(a);
                let x = self.inst(&x, v);
                let y = self.inst(&y, v);
                self.conv(x, y, None, face)
            }
            (Val::Path(x, l, r), Val::Path(y, m, n)) => {
                let i = self.fresh_dim();
                let x_body = self.inst_dim(&x, Dim::Var(i));
                let y_body = self.inst_dim(&y, Dim::Var(i));
                if !self.conv(x_body, y_body, None, face)? {
                    return Ok(false);
                }
                let a = self.inst_dim(&x, Dim::Zero);
                let b = self.inst_dim(&x, Dim::One);
                Ok(self.conv(l, m, Some(a), face)? && self.conv(r, n, Some(b), face)?)
            }
            (Val::Suc(a), Val::Suc(b)) => {
                let ty = self.alloc(Val::Nat);
                self.conv(a, b, Some(ty), face)
            }
            (Val::App(f, a), Val::App(g, b)) => {
                if !self.conv(f, g, None, face)? {
                    return Ok(false);
                }
                let ft = self.neutral_type(f, face)?;
                let ft = self.force(ft, face)?;
                let ty = if let Val::Pi(a, _) = self.get(ft) {
                    Some(a)
                } else {
                    None
                };
                self.conv(a, b, ty, face)
            }
            (Val::Fst(a), Val::Fst(b)) | (Val::Snd(a), Val::Snd(b)) => self.conv(a, b, None, face),
            (Val::PApp(a, i), Val::PApp(b, j)) => {
                Ok(self.faces.equal(face, i, j)? && self.conv(a, b, None, face)?)
            }
            (Val::If(p, a, b, c), Val::If(q, d, e, f)) => {
                let bool_ty = self.alloc(Val::Bool);
                let x = self.fresh_term();
                let u = self.alloc(Val::U(0));
                let motive = self.alloc(Val::Pi(bool_ty, Binder { var: x, body: u }));
                // Motive universes need not be U0; function eta only needs the domain here.
                if !self.conv(p, q, Some(motive), face)? || !self.conv(c, f, Some(bool_ty), face)? {
                    return Ok(false);
                }
                let tv = self.alloc(Val::True);
                let fv = self.alloc(Val::False);
                let ta = self.app(p, tv);
                let tb = self.app(p, fv);
                Ok(self.conv(a, d, Some(ta), face)? && self.conv(b, e, Some(tb), face)?)
            }
            (Val::NatElim(p, z, s, n), Val::NatElim(q, w, t, m)) => {
                let nat = self.alloc(Val::Nat);
                let x = self.variable(nat);
                let px = self.app(p, x);
                let qx = self.app(q, x);
                if !self.conv(px, qx, None, face)? || !self.conv(n, m, Some(nat), face)? {
                    return Ok(false);
                }
                let zero = self.alloc(Val::Zero);
                let pz = self.app(p, zero);
                if !self.conv(z, w, Some(pz), face)? {
                    return Ok(false);
                }
                let ih = self.variable(px);
                let sx = self.app(s, x);
                let tx = self.app(t, x);
                let sx = self.app(sx, ih);
                let tx = self.app(tx, ih);
                let next = self.alloc(Val::Suc(x));
                let pn = self.app(p, next);
                self.conv(sx, tx, Some(pn), face)
            }
            (Val::Com(a), Val::Com(b)) => {
                if !self.faces.equal(face, a.from, b.from)?
                    || !self.faces.equal(face, a.to, b.to)?
                {
                    return Ok(false);
                }
                let i = self.fresh_dim();
                let d = Dim::Var(i);
                let af = self.restrict(a.family, a.dim, d);
                let bf = self.restrict(b.family, b.dim, d);
                if !self.conv(af, bf, None, face)? {
                    return Ok(false);
                }
                let src = self.restrict(a.family, a.dim, a.from);
                if !self.conv(a.cap, b.cap, Some(src), face)? {
                    return Ok(false);
                }
                let mut ac = self.faces.bot();
                let mut bc = self.faces.bot();
                for (f, _) in &a.tubes {
                    ac = self.faces.or(ac, *f);
                }
                for (f, _) in &b.tubes {
                    bc = self.faces.or(bc, *f);
                }
                let ac = self.faces.and(face, ac);
                let bc = self.faces.and(face, bc);
                if !self.faces.entails(ac, bc)? || !self.faces.entails(bc, ac)? {
                    return Ok(false);
                }
                for (f, x) in a.tubes {
                    for &(g, y) in &b.tubes {
                        let overlap = self.faces.and(f, g);
                        let overlap = self.faces.and(face, overlap);
                        let x = self.restrict(x, a.dim, d);
                        let y = self.restrict(y, b.dim, d);
                        if !self.conv(x, y, Some(af), overlap)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            (Val::Glue(a, bs), Val::Glue(b, cs)) => {
                if !self.conv(a, b, None, face)? {
                    return Ok(false);
                }
                let mut ac = self.faces.bot();
                let mut bc = self.faces.bot();
                for (f, _, _) in &bs {
                    ac = self.faces.or(ac, *f);
                }
                for (f, _, _) in &cs {
                    bc = self.faces.or(bc, *f);
                }
                let ac = self.faces.and(face, ac);
                let bc = self.faces.and(face, bc);
                if !self.faces.entails(ac, bc)? || !self.faces.entails(bc, ac)? {
                    return Ok(false);
                }
                for (f, t, e) in bs {
                    for &(g, u, q) in &cs {
                        let overlap = self.faces.and(f, g);
                        let overlap = self.faces.and(face, overlap);
                        let eqty = self.equiv_type(t, a);
                        if !self.conv(t, u, None, overlap)?
                            || !self.conv(e, q, Some(eqty), overlap)?
                        {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            (Val::Unglue(g, x), Val::Unglue(h, y)) => {
                Ok(self.conv(g, h, None, face)? && self.conv(x, y, None, face)?)
            }
            _ => Ok(false),
        }
    }
}

#[cfg(test)]
mod inductive_core_tests {
    use super::*;
    use crate::syntax::{Program, TelescopeEntry};

    fn entry(program: &mut Program, name: &str, ty: Term) -> TelescopeEntry {
        TelescopeEntry {
            name: name.to_owned(),
            ty: program.alloc(ty, 0),
        }
    }

    fn check_all(program: &Program) -> Result<()> {
        for index in 0..program.decls.len() {
            let mut engine = Engine::new(program, true, 100_000, 50_000);
            engine.check_declaration(index)?;
        }
        Ok(())
    }

    #[test]
    fn checks_recursive_nat_family_and_constructors() {
        let mut program = Program::default();
        let nat = program.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        let zero = program.push_constructor(nat, "uzero".to_owned(), vec![], vec![], vec![]);
        let pred = entry(&mut program, "pred", Term::Inductive(nat));
        let suc = program.push_constructor(nat, "usuc".to_owned(), vec![pred], vec![], vec![0]);

        let nat_ty = program.alloc(Term::Inductive(nat), 0);
        let zero_term = program.alloc(Term::Constructor(zero), 0);
        program.push_decl("z".to_owned(), nat_ty, zero_term);

        let nat_ty = program.alloc(Term::Inductive(nat), 0);
        let suc_term = program.alloc(Term::Constructor(suc), 0);
        let zero_term = program.alloc(Term::Constructor(zero), 0);
        let one = program.alloc(Term::App(suc_term, zero_term), 0);
        program.push_decl("one".to_owned(), nat_ty, one);

        check_all(&program).unwrap();
    }

    #[test]
    fn checks_recursive_nat_eliminator() {
        let mut program = Program::default();
        let nat = program.push_inductive("UserNat".to_owned(), 0, vec![], vec![]);
        let uzero = program.push_constructor(nat, "uzero".to_owned(), vec![], vec![], vec![]);
        let pred = entry(&mut program, "pred", Term::Inductive(nat));
        let usuc = program.push_constructor(nat, "usuc".to_owned(), vec![pred], vec![], vec![0]);

        let nat_result = program.alloc(Term::Nat, 0);
        let motive = program.alloc(Term::Lam(nat_result), 0);
        let zero_method = program.alloc(Term::Zero, 0);
        let ih = program.alloc(Term::Var(0), 0);
        let suc_ih = program.alloc(Term::Suc(ih), 0);
        let suc_ih = program.alloc(Term::Lam(suc_ih), 0);
        let suc_method = program.alloc(Term::Lam(suc_ih), 0);

        let usuc_head = program.alloc(Term::Constructor(usuc), 0);
        let uzero_term = program.alloc(Term::Constructor(uzero), 0);
        let one = program.alloc(Term::App(usuc_head, uzero_term), 0);
        let elim = program.alloc(
            Term::Elim {
                inductive: nat,
                parameters: vec![],
                motive,
                methods: vec![zero_method, suc_method],
                indices: vec![],
                scrutinee: one,
            },
            0,
        );
        let expected = program.alloc(Term::Nat, 0);
        program.push_decl("fold-one".to_owned(), expected, elim);

        check_all(&program).unwrap();
    }

    #[test]
    fn checks_dependent_vec_eliminator() {
        let mut program = Program::default();
        let type0 = program.alloc(Term::U(0), 0);
        let nat_ty = program.alloc(Term::Nat, 0);
        let vec = program.push_inductive(
            "Vec".to_owned(),
            0,
            vec![TelescopeEntry {
                name: "A".to_owned(),
                ty: type0,
            }],
            vec![TelescopeEntry {
                name: "length".to_owned(),
                ty: nat_ty,
            }],
        );

        let zero_index = program.alloc(Term::Zero, 0);
        let nil = program.push_constructor(vec, "nil".to_owned(), vec![], vec![zero_index], vec![]);

        let n_arg = entry(&mut program, "n", Term::Nat);
        let a_var = program.alloc(Term::Var(1), 0);
        let head_arg = TelescopeEntry {
            name: "head".to_owned(),
            ty: a_var,
        };
        let vec_head = program.alloc(Term::Inductive(vec), 0);
        let a_var = program.alloc(Term::Var(2), 0);
        let vec_a = program.alloc(Term::App(vec_head, a_var), 0);
        let n_var = program.alloc(Term::Var(1), 0);
        let vec_a_n = program.alloc(Term::App(vec_a, n_var), 0);
        let tail_arg = TelescopeEntry {
            name: "tail".to_owned(),
            ty: vec_a_n,
        };
        let n_result = program.alloc(Term::Var(2), 0);
        let suc_n = program.alloc(Term::Suc(n_result), 0);
        let cons = program.push_constructor(
            vec,
            "cons".to_owned(),
            vec![n_arg, head_arg, tail_arg],
            vec![suc_n],
            vec![2],
        );

        // P = λ n. λ xs. Nat
        let motive_result = program.alloc(Term::Nat, 0);
        let motive_xs = program.alloc(Term::Lam(motive_result), 0);
        let motive = program.alloc(Term::Lam(motive_xs), 0);
        let nil_method = program.alloc(Term::Zero, 0);

        // cons_case = λ n. λ head. λ tail. λ ih. suc ih
        let ih = program.alloc(Term::Var(0), 0);
        let suc_ih = program.alloc(Term::Suc(ih), 0);
        let cons_method = program.alloc(Term::Lam(suc_ih), 0);
        let cons_method = program.alloc(Term::Lam(cons_method), 0);
        let cons_method = program.alloc(Term::Lam(cons_method), 0);
        let cons_method = program.alloc(Term::Lam(cons_method), 0);

        let bool_ty = program.alloc(Term::Bool, 0);
        let cons_head = program.alloc(Term::Constructor(cons), 0);
        let cons_bool = program.alloc(Term::App(cons_head, bool_ty), 0);
        let zero = program.alloc(Term::Zero, 0);
        let cons_zero = program.alloc(Term::App(cons_bool, zero), 0);
        let true_term = program.alloc(Term::True, 0);
        let cons_true = program.alloc(Term::App(cons_zero, true_term), 0);
        let nil_head = program.alloc(Term::Constructor(nil), 0);
        let bool_ty_arg = program.alloc(Term::Bool, 0);
        let nil_bool = program.alloc(Term::App(nil_head, bool_ty_arg), 0);
        let singleton = program.alloc(Term::App(cons_true, nil_bool), 0);

        let bool_parameter = program.alloc(Term::Bool, 0);
        let one_index = program.alloc(Term::Suc(zero), 0);
        let elim = program.alloc(
            Term::Elim {
                inductive: vec,
                parameters: vec![bool_parameter],
                motive,
                methods: vec![nil_method, cons_method],
                indices: vec![one_index],
                scrutinee: singleton,
            },
            0,
        );
        let expected = program.alloc(Term::Nat, 0);
        program.push_decl("vec-length-one".to_owned(), expected, elim);

        check_all(&program).unwrap();
    }

    #[test]
    fn checks_indexed_vec_nil_constructor() {
        let mut program = Program::default();
        let type0 = program.alloc(Term::U(0), 0);
        let nat_ty = program.alloc(Term::Nat, 0);
        let vec = program.push_inductive(
            "Vec".to_owned(),
            0,
            vec![TelescopeEntry {
                name: "A".to_owned(),
                ty: type0,
            }],
            vec![TelescopeEntry {
                name: "length".to_owned(),
                ty: nat_ty,
            }],
        );
        let zero_index = program.alloc(Term::Zero, 0);
        let nil = program.push_constructor(vec, "nil".to_owned(), vec![], vec![zero_index], vec![]);

        let vec_head = program.alloc(Term::Inductive(vec), 0);
        let bool_ty = program.alloc(Term::Bool, 0);
        let vec_bool = program.alloc(Term::App(vec_head, bool_ty), 0);
        let zero = program.alloc(Term::Zero, 0);
        let expected = program.alloc(Term::App(vec_bool, zero), 0);

        let nil_head = program.alloc(Term::Constructor(nil), 0);
        let bool_arg = program.alloc(Term::Bool, 0);
        let body = program.alloc(Term::App(nil_head, bool_arg), 0);
        program.push_decl("nil-bool".to_owned(), expected, body);

        check_all(&program).unwrap();
    }
}
