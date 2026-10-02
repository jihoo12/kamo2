//! Slice C publication and runtime helpers. No higher eliminator or Kan rule.
#[cfg(test)]
#[path = "hit_runtime_tests.rs"]
mod tests;
use super::*;
use crate::eval::{Engine, Env, EnvId, Val, ValId};
use crate::face::{Dim, FaceId};
use crate::syntax::{FamilyConstructors, InductiveDecl, Program};

impl SemanticallyCheckedHigherMetadata<'_> {
    /// Explicit executable capability gate; B certification alone remains inert.
    pub(crate) fn publish(&self) -> Result<Program> {
        require(
            self.raw.higher.iter().all(|h| h.dimensions.len() == 1),
            "Slice C supports exactly one dimension",
        )?;
        require(
            self.raw.terms.len() <= MAX_TERM_NODES,
            "publication syntax budget exhausted",
        )?;
        let mut program = Program::default();
        copy_metadata_terms(&self.raw.terms, &mut program.terms);
        program.inductives = self
            .raw
            .families
            .iter()
            .map(|f| InductiveDecl {
                id: f.id,
                name: f.name.clone(),
                universe: f.universe,
                parameters: f.parameters.clone(),
                indices: f.indices.clone(),
                constructors: FamilyConstructors::Higher(f.constructors.clone()),
            })
            .collect();
        program.constructors = self.raw.points.clone();
        program.higher = self.raw.higher.clone();
        Ok(program)
    }
}

// Only the whitelist has recursively flat payloads. Preserve IDs without ever
// cloning unvalidated unused Com/System/Glue faces. A rejects the sentinel if
// an unsupported node is actually referenced by metadata.
fn copy_metadata_terms(from: &Arena<TermId, Node>, to: &mut Arena<TermId, Node>) {
    for index in 0..from.len() {
        let node = from.get(TermId::new(index));
        let term = match &node.term {
            Term::Var(_)
            | Term::U(_)
            | Term::Pi(..)
            | Term::Sigma(..)
            | Term::App(..)
            | Term::Ann(..)
            | Term::Path(..)
            | Term::Suc(_)
            | Term::Inductive(_)
            | Term::Constructor(_)
            | Term::Bool
            | Term::Nat
            | Term::True
            | Term::False
            | Term::Zero => node.term.clone(),
            _ => Term::Global(usize::MAX),
        };
        to.alloc(Node {
            term,
            offset: node.offset,
        });
    }
}

/// CheckedProgram rechecks published signatures, including forged internal
/// Programs. C deliberately supports all-Higher signatures or ordinary programs,
/// not mixed imports yet; this cannot silently erase a Higher membership.
pub(crate) fn validate_executable(program: &Program) -> Result<()> {
    require(
        program.terms.len() <= MAX_TERM_NODES,
        "executable syntax budget exhausted",
    )?;
    require(
        program.inductives.len() <= MAX_FAMILIES,
        "family count budget exhausted",
    )?;
    require(
        program.constructors.len() <= MAX_CONSTRUCTORS
            && program.higher.len() <= MAX_CONSTRUCTORS - program.constructors.len(),
        "constructor count budget exhausted",
    )?;
    let mut budget = Budget::default();
    for h in &program.higher {
        require(
            h.dimensions.len() == 1,
            "Slice C supports exactly one dimension",
        )?;
        require(
            h.arguments.len() <= MAX_TELESCOPE && h.result_indices.len() <= MAX_TELESCOPE,
            "telescope budget exhausted",
        )?;
        require(
            h.boundary.pieces.len() <= MAX_PIECES_PER_CONSTRUCTOR,
            "boundary piece budget exhausted",
        )?;
        for piece in &h.boundary.pieces {
            let mut pending = vec![(&piece.face, 0)];
            while let Some((face, depth)) = pending.pop() {
                budget.face(depth)?;
                if let F::And(a, b) | F::Or(a, b) = face {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
            }
        }
    }
    let mut raw = RawHigherMetadata::default();
    for f in &program.inductives {
        require(
            f.parameters.len() <= MAX_TELESCOPE && f.indices.len() <= MAX_TELESCOPE,
            "telescope budget exhausted",
        )?;
        let FamilyConstructors::Higher(members) = &f.constructors else {
            return Err(Error::plain(
                "Slice C mixed Ordinary/Higher signatures are not supported",
            ));
        };
        require(
            members.len() <= MAX_CONSTRUCTORS,
            "membership budget exhausted",
        )?;
        raw.families.push(HigherFamilyDecl {
            id: f.id,
            name: String::new(),
            universe: f.universe,
            parameters: f.parameters.clone(),
            indices: f.indices.clone(),
            constructors: members.clone(),
        });
    }
    for point in &program.constructors {
        require(
            point.arguments.len() <= MAX_TELESCOPE && point.result_indices.len() <= MAX_TELESCOPE,
            "telescope budget exhausted",
        )?;
    }
    copy_metadata_terms(&program.terms, &mut raw.terms);
    raw.points = program.constructors.clone();
    raw.higher = program.higher.clone();
    raw.validate()?.validate_semantic()?;
    validate_runtime_terms(program)
}

impl Program {
    pub(crate) fn higher_constructor(
        &self,
        id: HigherConstructorId,
    ) -> Result<&HigherConstructorDecl> {
        let h = self
            .higher
            .get(id.index())
            .ok_or_else(|| Error::plain("missing higher constructor"))?;
        require(
            h.id == id && h.dimensions.len() == 1,
            "unsupported higher constructor",
        )?;
        let f = self
            .inductives
            .get(h.inductive.index())
            .ok_or_else(|| Error::plain("missing higher owner"))?;
        require(
            matches!(&f.constructors, FamilyConstructors::Higher(ids)
            if ids.contains(&ConstructorRef::Higher(id))),
            "higher constructor ownership mismatch",
        )?;
        Ok(h)
    }
}

impl Engine<'_> {
    pub(crate) fn higher_environment(
        &mut self,
        id: HigherConstructorId,
        parameters: &[ValId],
        arguments: &[ValId],
        dimensions: &[Dim],
    ) -> Result<EnvId> {
        let h = self.program.higher_constructor(id)?;
        let f = self
            .program
            .inductives
            .get(h.inductive.index())
            .ok_or_else(|| Error::plain("missing higher owner"))?;
        require(
            parameters.len() == f.parameters.len()
                && arguments.len() == h.arguments.len()
                && dimensions.len() == 1,
            "higher application arity mismatch",
        )?;
        let mut terms = parameters.to_vec();
        terms.extend_from_slice(arguments);
        Ok(self.env(Env {
            terms,
            dims: dimensions.to_vec(),
        }))
    }

    pub(crate) fn higher_result(
        &mut self,
        id: HigherConstructorId,
        parameters: &[ValId],
        arguments: &[ValId],
        dimensions: &[Dim],
    ) -> Result<ValId> {
        let env = self.higher_environment(id, parameters, arguments, dimensions)?;
        let h = self.program.higher_constructor(id)?.clone();
        let mut result = self.alloc(Val::Inductive(h.inductive));
        for p in parameters {
            result = self.app(result, *p);
        }
        for index in h.result_indices {
            let value = self.thunk(index, env);
            result = self.app(result, value);
        }
        Ok(result)
    }

    pub(crate) fn higher_boundary(
        &mut self,
        id: HigherConstructorId,
        parameters: &[ValId],
        arguments: &[ValId],
        dimensions: &[Dim],
        face: FaceId,
    ) -> Result<Option<ValId>> {
        let env = self.higher_environment(id, parameters, arguments, dimensions)?;
        let h = self.program.higher_constructor(id)?.clone();
        for piece in &h.boundary.pieces {
            self.tick()?;
            let active = self.face(&piece.face, env);
            if self.faces.entails(face, active)? {
                return Ok(Some(self.thunk(piece.term, env)));
            }
        }
        Ok(None)
    }

    // Sufficient congruence only. Call after boundary forcing; different heads
    // are not disjoint since their boundaries can compute to the same point.
    pub(crate) fn higher_congruent(&mut self, a: ValId, b: ValId, face: FaceId) -> Result<bool> {
        let (
            Val::HigherApp {
                constructor: x,
                parameters: ps,
                arguments: args,
                dimensions: ds,
            },
            Val::HigherApp {
                constructor: y,
                parameters: qs,
                arguments: other,
                dimensions: es,
            },
        ) = (self.get(a), self.get(b))
        else {
            return Ok(false);
        };
        if x != y || ps.len() != qs.len() || args.len() != other.len() || ds.len() != es.len() {
            return Ok(false);
        }
        let h = self.program.higher_constructor(x)?.clone();
        let f = self.program.inductives[h.inductive.index()].clone();
        let mut env = self.env(Env::default());
        for ((left, right), entry) in ps
            .into_iter()
            .chain(args)
            .zip(qs.into_iter().chain(other))
            .zip(f.parameters.iter().chain(&h.arguments))
        {
            let ty = self.thunk(entry.ty, env);
            if !self.conv(left, right, Some(ty), face)? {
                return Ok(false);
            }
            let mut next = self.environment(env);
            next.terms.push(left);
            env = self.env(next);
        }
        for (d, e) in ds.into_iter().zip(es) {
            if !self.faces.equal(face, d, e)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn validate_runtime_terms(program: &Program) -> Result<()> {
    enum Visit {
        Enter(TermId, Scope, usize),
        Exit(TermId),
    }
    let mut budget = Budget::default();
    for (global_limit, decl) in program.decls.iter().enumerate() {
        for root in [decl.ty, decl.body] {
            let mut pending = vec![Visit::Enter(
                root,
                Scope {
                    terms: 0,
                    dimensions: 0,
                },
                0,
            )];
            let mut active = HashSet::new();
            while let Some(visit) = pending.pop() {
                budget.work(1)?;
                let Visit::Enter(id, scope, depth) = visit else {
                    if let Visit::Exit(id) = visit {
                        active.remove(&id);
                    }
                    continue;
                };
                budget.term(depth)?;
                require(
                    id.index() < program.terms.len(),
                    "invalid executable term ID",
                )?;
                require(active.insert(id), "cyclic executable term graph")?;
                pending.push(Visit::Exit(id));
                let mut child = |id, scope| pending.push(Visit::Enter(id, scope, depth + 1));
                let term_scope = Scope {
                    terms: scope.terms + 1,
                    ..scope
                };
                let dim_scope = Scope {
                    dimensions: scope.dimensions + 1,
                    ..scope
                };
                let dimension = |d: D| -> Result<()> {
                    require(
                        !matches!(d, D::Bound(i) if i >= scope.dimensions),
                        "escaped executable dimension",
                    )
                };
                let mut face = |f: &F| -> Result<()> {
                    let mut faces = vec![(f, 0)];
                    while let Some((f, depth)) = faces.pop() {
                        budget.face(depth)?;
                        match f {
                            F::Eq(a, b) => {
                                dimension(*a)?;
                                dimension(*b)?;
                            }
                            F::And(a, b) | F::Or(a, b) => {
                                faces.push((a, depth + 1));
                                faces.push((b, depth + 1));
                            }
                            F::Top | F::Bot => {}
                        }
                    }
                    Ok(())
                };
                match &program.terms.get(id).term {
                    Term::Var(i) => require(*i < scope.terms, "escaped executable term variable")?,
                    Term::Global(i) => {
                        require(*i < global_limit, "forward executable global reference")?
                    }
                    Term::Inductive(i) => require(
                        i.index() < program.inductives.len(),
                        "missing executable family",
                    )?,
                    Term::Constructor(i) => require(
                        i.index() < program.constructors.len(),
                        "missing executable point",
                    )?,
                    Term::HigherApp {
                        constructor,
                        parameters,
                        arguments,
                        dimensions,
                    } => {
                        let h = program.higher_constructor(*constructor)?;
                        let f = &program.inductives[h.inductive.index()];
                        require(
                            parameters.len() == f.parameters.len()
                                && arguments.len() == h.arguments.len()
                                && dimensions.len() == 1,
                            "higher application arity mismatch",
                        )?;
                        for d in dimensions {
                            dimension(*d)?;
                        }
                        for t in parameters.iter().chain(arguments) {
                            child(*t, scope);
                        }
                    }
                    Term::Pi(a, b) | Term::Sigma(a, b) => {
                        child(*a, scope);
                        child(*b, term_scope);
                    }
                    Term::Lam(t) => child(*t, term_scope),
                    Term::PLam(t) => child(*t, dim_scope),
                    Term::Path(a, l, r) => {
                        child(*a, dim_scope);
                        child(*l, scope);
                        child(*r, scope);
                    }
                    Term::App(a, b) | Term::Pair(a, b) | Term::Ann(a, b) | Term::Unglue(a, b) => {
                        child(*a, scope);
                        child(*b, scope);
                    }
                    Term::Suc(t) | Term::Fst(t) | Term::Snd(t) => child(*t, scope),
                    Term::PApp(t, d) => {
                        child(*t, scope);
                        dimension(*d)?;
                    }
                    Term::If(a, b, c, d) | Term::NatElim(a, b, c, d) => {
                        for t in [a, b, c, d] {
                            child(*t, scope);
                        }
                    }
                    Term::Elim {
                        inductive,
                        parameters,
                        motive,
                        methods,
                        indices,
                        scrutinee,
                    } => {
                        program
                            .inductives
                            .get(inductive.index())
                            .ok_or_else(|| Error::plain("missing eliminator family"))?
                            .constructors
                            .ordinary()?;
                        for t in parameters
                            .iter()
                            .chain(methods)
                            .chain(indices)
                            .chain([motive, scrutinee])
                        {
                            child(*t, scope);
                        }
                    }
                    Term::Com {
                        family,
                        from,
                        to,
                        cap,
                        tubes,
                    } => {
                        dimension(*from)?;
                        dimension(*to)?;
                        child(*family, dim_scope);
                        child(*cap, scope);
                        for (f, t) in tubes {
                            face(f)?;
                            child(*t, dim_scope);
                        }
                    }
                    Term::System(a, bs) => {
                        child(*a, scope);
                        for (f, t) in bs {
                            face(f)?;
                            child(*t, scope);
                        }
                    }
                    Term::Glue(a, bs) => {
                        child(*a, scope);
                        for (f, t, e) in bs {
                            face(f)?;
                            child(*t, scope);
                            child(*e, scope);
                        }
                    }
                    Term::GlueIntro(a, b, bs) => {
                        child(*a, scope);
                        child(*b, scope);
                        for (f, t) in bs {
                            face(f)?;
                            child(*t, scope);
                        }
                    }
                    Term::U(_) | Term::Bool | Term::Nat | Term::Zero | Term::True | Term::False => {
                    }
                }
            }
        }
    }
    Ok(())
}
