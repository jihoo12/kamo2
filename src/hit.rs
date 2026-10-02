//! Slice A only: isolated, structurally checked higher metadata.
//!
//! IDs resolve within this staging arena/tables, never an executable Program.
//! The certificate borrows the entire raw input immutably; there is no export
//! to Program/CheckedProgram and no evaluator or semantic-checker consumer.
// This subsystem intentionally has no production caller until a later slice.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};

use crate::arena::{Arena, Key, key};
use crate::syntax::{
    ConstructorDecl, ConstructorId, D, F, InductiveId, Node, Telescope, Term, TermId,
};
use crate::{Error, Result};

key!(HigherConstructorId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ConstructorRef {
    Point(ConstructorId),
    Higher(HigherConstructorId),
}

#[derive(Debug)]
pub(crate) struct HigherFamilyDecl {
    pub id: InductiveId,
    pub name: String,
    pub universe: u32,
    pub parameters: Telescope,
    pub indices: Telescope,
    pub constructors: Vec<ConstructorRef>,
}

pub(crate) type DimensionTelescope = Vec<String>;

#[derive(Debug)]
pub(crate) struct HigherConstructorDecl {
    pub id: HigherConstructorId,
    pub inductive: InductiveId,
    pub name: String,
    pub arguments: Telescope,
    pub dimensions: DimensionTelescope,
    pub result_indices: Vec<TermId>,
    pub boundary: PartialConstructorBoundary,
}

#[derive(Debug, Default)]
pub(crate) struct PartialConstructorBoundary {
    pub pieces: Vec<BoundaryPiece>,
}

#[derive(Debug)]
pub(crate) struct BoundaryPiece {
    pub face: F,
    pub term: TermId,
}

#[derive(Debug, Default)]
pub(crate) struct RawHigherMetadata {
    pub terms: Arena<TermId, Node>,
    pub families: Vec<HigherFamilyDecl>,
    pub points: Vec<ConstructorDecl>,
    pub higher: Vec<HigherConstructorDecl>,
}

/// Not a semantic certificate. The private field prevents unchecked creation;
/// its lifetime prevents mutation of any certified term or declaration.
#[derive(Debug)]
pub(crate) struct StructurallyCheckedHigherMetadata<'a> {
    raw: &'a RawHigherMetadata,
}

impl StructurallyCheckedHigherMetadata<'_> {
    pub(crate) fn families(&self) -> &[HigherFamilyDecl] {
        &self.raw.families
    }

    pub(crate) fn higher(&self) -> &[HigherConstructorDecl] {
        &self.raw.higher
    }
}

const MAX_FAMILIES: usize = 128;
const MAX_CONSTRUCTORS: usize = 4096; // combined point + higher tables
const MAX_DIMENSIONS: usize = 16;
const MAX_TELESCOPE: usize = 256;
const MAX_PIECES_PER_CONSTRUCTOR: usize = 256;
const MAX_PIECES: usize = 4096;
const MAX_TERM_NODES: usize = 100_000;
const MAX_FACE_NODES: usize = 32_768;
const MAX_DEPTH: usize = 128;
const MAX_WORK: usize = 200_000;

fn require(condition: bool, message: &str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(Error::plain(format!("higher metadata: {message}")))
    }
}

#[derive(Default)]
struct Budget {
    work: usize,
    terms: usize,
    faces: usize,
    pieces: usize,
}

impl Budget {
    fn work(&mut self, amount: usize) -> Result<()> {
        require(
            amount <= MAX_WORK - self.work,
            "total work budget exhausted",
        )?;
        self.work += amount;
        Ok(())
    }

    fn term(&mut self, depth: usize) -> Result<()> {
        self.work(1)?;
        require(depth <= MAX_DEPTH, "traversal depth budget exhausted")?;
        require(
            self.terms < MAX_TERM_NODES,
            "term traversal budget exhausted",
        )?;
        self.terms += 1;
        Ok(())
    }

    fn face(&mut self, depth: usize) -> Result<()> {
        self.work(1)?;
        require(depth <= MAX_DEPTH, "traversal depth budget exhausted")?;
        require(
            self.faces < MAX_FACE_NODES,
            "face traversal budget exhausted",
        )?;
        self.faces += 1;
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct Scope {
    terms: usize,
    dimensions: usize,
}

struct Validator<'a> {
    raw: &'a RawHigherMetadata,
    budget: Budget,
    positions: HashMap<ConstructorRef, usize>,
}

impl RawHigherMetadata {
    pub(crate) fn validate(&self) -> Result<StructurallyCheckedHigherMetadata<'_>> {
        let mut validator = Validator {
            raw: self,
            budget: Budget::default(),
            positions: HashMap::new(),
        };
        validator.validate()?;
        Ok(StructurallyCheckedHigherMetadata { raw: self })
    }
}

impl<'a> Validator<'a> {
    fn family(&self, id: InductiveId) -> Result<&'a HigherFamilyDecl> {
        let family = self
            .raw
            .families
            .get(id.index())
            .ok_or_else(|| Error::plain("higher metadata: missing family"))?;
        require(family.id == id, "family ID does not match table position")?;
        Ok(family)
    }

    fn point(&self, id: ConstructorId) -> Result<&'a ConstructorDecl> {
        let point = self
            .raw
            .points
            .get(id.index())
            .ok_or_else(|| Error::plain("higher metadata: missing point constructor"))?;
        require(point.id == id, "point ID does not match table position")?;
        self.family(point.inductive)?;
        Ok(point)
    }

    fn higher(&self, id: HigherConstructorId) -> Result<&'a HigherConstructorDecl> {
        let higher = self
            .raw
            .higher
            .get(id.index())
            .ok_or_else(|| Error::plain("higher metadata: missing higher constructor"))?;
        require(higher.id == id, "higher ID does not match table position")?;
        self.family(higher.inductive)?;
        Ok(higher)
    }

    fn node(&self, id: TermId) -> Result<&'a Term> {
        // Arena::get is unchecked. Never call it before this range check.
        require(id.index() < self.raw.terms.len(), "invalid term ID")?;
        Ok(&self.raw.terms.get(id).term)
    }

    fn validate(&mut self) -> Result<()> {
        require(
            self.raw.families.len() <= MAX_FAMILIES,
            "family count budget exhausted",
        )?;
        require(
            self.raw.points.len() <= MAX_CONSTRUCTORS,
            "constructor count budget exhausted",
        )?;
        require(
            self.raw.higher.len() <= MAX_CONSTRUCTORS - self.raw.points.len(),
            "constructor count budget exhausted",
        )?;
        // Preflight all identities and membership before visiting any syntax.
        for (index, family) in self.raw.families.iter().enumerate() {
            self.budget.work(1)?;
            require(
                family.id.index() == index,
                "family ID does not match table position",
            )?;
            self.budget.work(family.constructors.len())?;
            let mut has_higher = false;
            for (position, member) in family.constructors.iter().copied().enumerate() {
                let owner = match member {
                    ConstructorRef::Point(id) => self.point(id)?.inductive,
                    ConstructorRef::Higher(id) => {
                        has_higher = true;
                        self.higher(id)?.inductive
                    }
                };
                require(owner == family.id, "member has wrong owner")?;
                require(
                    self.positions.insert(member, position).is_none(),
                    "duplicate membership",
                )?;
            }
            require(has_higher, "staged family has no higher constructor")?;
        }
        for (index, point) in self.raw.points.iter().enumerate() {
            self.budget.work(1)?;
            require(
                point.id.index() == index,
                "point ID does not match table position",
            )?;
            self.family(point.inductive)?;
            require(
                self.positions
                    .contains_key(&ConstructorRef::Point(point.id)),
                "orphan point constructor",
            )?;
        }
        for (index, higher) in self.raw.higher.iter().enumerate() {
            self.budget.work(1)?;
            require(
                higher.id.index() == index,
                "higher ID does not match table position",
            )?;
            self.family(higher.inductive)?;
            require(
                self.positions
                    .contains_key(&ConstructorRef::Higher(higher.id)),
                "orphan higher constructor",
            )?;
        }
        for family in &self.raw.families {
            let parameters = self.telescope(&family.parameters, 0, family.id)?;
            self.telescope(&family.indices, parameters, family.id)?;
        }
        for point in &self.raw.points {
            require(
                point.recursive_arguments.is_empty(),
                "recursive annotations forbidden in staged family",
            )?;
            let family = self.family(point.inductive)?;
            let terms = self.telescope(&point.arguments, family.parameters.len(), family.id)?;
            self.indices(
                &point.result_indices,
                family,
                Scope {
                    terms,
                    dimensions: 0,
                },
            )?;
        }
        for higher in &self.raw.higher {
            let family = self.family(higher.inductive)?;
            require(
                !higher.dimensions.is_empty(),
                "higher constructor needs dimensions",
            )?;
            require(
                higher.dimensions.len() <= MAX_DIMENSIONS,
                "dimension count budget exhausted",
            )?;
            self.budget.work(higher.dimensions.len())?;
            let terms = self.telescope(&higher.arguments, family.parameters.len(), family.id)?;
            let scope = Scope {
                terms,
                dimensions: higher.dimensions.len(),
            };
            self.indices(&higher.result_indices, family, scope)?;
            let pieces = &higher.boundary.pieces;
            require(
                pieces.len() <= MAX_PIECES_PER_CONSTRUCTOR,
                "boundary piece budget exhausted",
            )?;
            require(
                pieces.len() <= MAX_PIECES - self.budget.pieces,
                "aggregate boundary piece budget exhausted",
            )?;
            self.budget.pieces += pieces.len();
            self.budget.work(pieces.len())?;
            let position = self.positions[&ConstructorRef::Higher(higher.id)];
            for piece in pieces {
                self.face(&piece.face, scope.dimensions)?;
                self.boundary(piece.term, family, position, scope)?;
            }
        }
        Ok(())
    }

    fn telescope(
        &mut self,
        telescope: &Telescope,
        mut terms: usize,
        owner: InductiveId,
    ) -> Result<usize> {
        require(
            telescope.len() <= MAX_TELESCOPE,
            "telescope budget exhausted",
        )?;
        self.budget.work(telescope.len())?;
        for entry in telescope {
            self.term(
                entry.ty,
                owner,
                Scope {
                    terms,
                    dimensions: 0,
                },
            )?;
            terms += 1;
        }
        Ok(terms)
    }

    fn indices(
        &mut self,
        indices: &[TermId],
        family: &HigherFamilyDecl,
        scope: Scope,
    ) -> Result<()> {
        require(
            indices.len() == family.indices.len(),
            "result-index arity mismatch",
        )?;
        self.budget.work(indices.len())?;
        for index in indices {
            self.term(*index, family.id, scope)?;
        }
        Ok(())
    }

    fn dimension(&mut self, dimension: D, bound: usize) -> Result<()> {
        self.budget.work(1)?;
        if let D::Bound(index) = dimension {
            require(index < bound, "escaped dimension variable")?;
        }
        Ok(())
    }

    fn face(&mut self, face: &F, dimensions: usize) -> Result<()> {
        let mut pending = vec![(face, 0)];
        while let Some((face, depth)) = pending.pop() {
            self.budget.face(depth)?;
            match face {
                F::Top | F::Bot => {}
                F::Eq(a, b) => {
                    self.dimension(*a, dimensions)?;
                    self.dimension(*b, dimensions)?;
                }
                F::And(a, b) | F::Or(a, b) => {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
            }
        }
        Ok(())
    }

    /// The ordinary metadata syntax whitelist, with separate binder namespaces
    /// and stricter current-family exclusion (including constructor constants).
    /// PApp/PLam and every other executable extension remain unsupported.
    fn term(&mut self, root: TermId, owner: InductiveId, scope: Scope) -> Result<()> {
        self.term_at_depth(root, owner, scope, 0)
    }

    fn term_at_depth(
        &mut self,
        root: TermId,
        owner: InductiveId,
        scope: Scope,
        depth: usize,
    ) -> Result<()> {
        enum Visit {
            Enter(TermId, Scope, usize),
            Exit(TermId),
        }
        let mut pending = vec![Visit::Enter(root, scope, depth)];
        let mut active = HashSet::new();
        while let Some(visit) = pending.pop() {
            self.budget.work(1)?;
            let Visit::Enter(id, scope, depth) = visit else {
                if let Visit::Exit(id) = visit {
                    active.remove(&id);
                }
                continue;
            };
            self.budget.term(depth)?;
            let node = self.node(id)?;
            require(active.insert(id), "cyclic term graph")?;
            pending.push(Visit::Exit(id));
            let mut child = |id, scope| pending.push(Visit::Enter(id, scope, depth + 1));
            match *node {
                Term::Var(index) => require(index < scope.terms, "escaped term variable")?,
                Term::Pi(a, b) | Term::Sigma(a, b) => {
                    child(a, scope);
                    child(
                        b,
                        Scope {
                            terms: scope.terms + 1,
                            ..scope
                        },
                    );
                }
                Term::App(a, b) | Term::Ann(a, b) => {
                    child(a, scope);
                    child(b, scope);
                }
                Term::Path(a, l, r) => {
                    child(
                        a,
                        Scope {
                            dimensions: scope.dimensions + 1,
                            ..scope
                        },
                    );
                    child(l, scope);
                    child(r, scope);
                }
                Term::Suc(a) => child(a, scope),
                Term::Inductive(id) => {
                    self.family(id)?;
                    require(id != owner, "current-family occurrence forbidden")?;
                    require(
                        id.index() < owner.index(),
                        "forward family reference forbidden",
                    )?;
                }
                Term::Constructor(id) => {
                    let point = self.point(id)?;
                    require(
                        point.inductive != owner,
                        "nested current-family constructor forbidden",
                    )?;
                    require(
                        point.inductive.index() < owner.index(),
                        "forward family reference forbidden",
                    )?;
                }
                Term::Global(_) => {
                    return Err(Error::plain("higher metadata: global alias forbidden"));
                }
                Term::U(_) | Term::Bool | Term::True | Term::False | Term::Nat | Term::Zero => {}
                _ => return Err(Error::plain("higher metadata: unsupported metadata term")),
            }
        }
        Ok(())
    }

    fn boundary(
        &mut self,
        root: TermId,
        family: &HigherFamilyDecl,
        position: usize,
        scope: Scope,
    ) -> Result<()> {
        let mut cursor = root;
        let mut arguments = Vec::new();
        let mut active = HashSet::new();
        let point = loop {
            self.budget.term(arguments.len())?;
            require(active.insert(cursor), "cyclic boundary application")?;
            match *self.node(cursor)? {
                Term::App(function, argument) => {
                    arguments.push((argument, arguments.len() + 1));
                    cursor = function;
                }
                Term::Constructor(id) => break self.point(id)?,
                _ => {
                    return Err(Error::plain(
                        "higher metadata: boundary must be an earlier point application",
                    ));
                }
            }
        };
        require(
            point.inductive == family.id,
            "boundary point has wrong owner",
        )?;
        let point_position = self
            .positions
            .get(&ConstructorRef::Point(point.id))
            .ok_or_else(|| Error::plain("higher metadata: orphan boundary point"))?;
        require(
            *point_position < position,
            "boundary point must be declared earlier",
        )?;
        require(
            arguments.len() == family.parameters.len() + point.arguments.len(),
            "boundary point application arity mismatch",
        )?;
        arguments.reverse();
        for (index, (argument, depth)) in arguments.iter().enumerate() {
            self.budget.work(1)?;
            self.term_at_depth(*argument, family.id, scope, *depth)?;
            if index < family.parameters.len() {
                let expected = scope.terms - 1 - index;
                require(
                    matches!(self.node(*argument)?, Term::Var(i) if *i == expected),
                    "boundary changes uniform parameter",
                )?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::TelescopeEntry;

    fn alloc(raw: &mut RawHigherMetadata, term: Term) -> TermId {
        raw.terms.alloc(Node { term, offset: 0 })
    }

    fn entry(name: &str, ty: TermId) -> TelescopeEntry {
        TelescopeEntry {
            name: name.into(),
            ty,
        }
    }

    fn circle() -> RawHigherMetadata {
        let mut raw = RawHigherMetadata::default();
        add_circle(&mut raw);
        raw
    }

    fn add_circle(raw: &mut RawHigherMetadata) {
        let owner = InductiveId::new(raw.families.len());
        let base = ConstructorId::new(raw.points.len());
        let loop_id = HigherConstructorId::new(raw.higher.len());
        let term = alloc(raw, Term::Constructor(base));
        raw.families.push(HigherFamilyDecl {
            id: owner,
            name: "Circle".into(),
            universe: 0,
            parameters: vec![],
            indices: vec![],
            constructors: vec![ConstructorRef::Point(base), ConstructorRef::Higher(loop_id)],
        });
        raw.points.push(ConstructorDecl {
            id: base,
            inductive: owner,
            name: "base".into(),
            arguments: vec![],
            result_indices: vec![],
            recursive_arguments: vec![],
        });
        raw.higher.push(HigherConstructorDecl {
            id: loop_id,
            inductive: owner,
            name: "loop".into(),
            arguments: vec![],
            dimensions: vec!["i".into()],
            result_indices: vec![],
            boundary: PartialConstructorBoundary {
                pieces: vec![
                    BoundaryPiece {
                        face: F::Eq(D::Bound(0), D::Zero),
                        term,
                    },
                    BoundaryPiece {
                        face: F::Eq(D::Bound(0), D::One),
                        term,
                    },
                ],
            },
        });
    }

    fn rejects(raw: &RawHigherMetadata, message: &str) {
        let error = raw.validate().unwrap_err();
        assert!(
            error.message.contains(message),
            "expected {message:?}, got {error}"
        );
    }

    #[test]
    fn valid_circle_is_only_structurally_certified() {
        let raw = circle();
        let checked = raw.validate().unwrap();
        assert_eq!(
            checked.families()[0].constructors,
            vec![
                ConstructorRef::Point(ConstructorId::new(0)),
                ConstructorRef::Higher(HigherConstructorId::new(0)),
            ]
        );
        let pieces = &checked.higher()[0].boundary.pieces;
        assert!(matches!(pieces[0].face, F::Eq(D::Bound(0), D::Zero)));
        assert!(matches!(pieces[1].face, F::Eq(D::Bound(0), D::One)));
        assert!(matches!(
            raw.terms.get(pieces[0].term).term,
            Term::Constructor(_)
        ));
        // No Program exists in this fixture; the certificate exposes no conversion.
        assert!(
            crate::CheckedProgram::check_surface(
                "data Circle : Type where\n  base : Circle\n  loop : base == base\n"
            )
            .is_err()
        );
    }

    #[test]
    fn malformed_table_ids_and_missing_owners() {
        let mut raw = circle();
        raw.higher[0].id = HigherConstructorId::new(42);
        rejects(&raw, "higher ID");
        let mut raw = circle();
        raw.higher[0].inductive = InductiveId::new(42);
        rejects(&raw, "missing family");
        let mut raw = circle();
        raw.points[0].id = ConstructorId::new(42);
        rejects(&raw, "point ID");
        let mut raw = circle();
        raw.points[0].inductive = InductiveId::new(42);
        rejects(&raw, "missing family");
        let mut raw = circle();
        raw.families[0].id = InductiveId::new(42);
        rejects(&raw, "family ID");
    }

    #[test]
    fn wrong_owner_membership_and_boundary_reference() {
        let mut raw = circle();
        add_circle(&mut raw);
        raw.families[0].constructors[0] = ConstructorRef::Point(ConstructorId::new(1));
        rejects(&raw, "member has wrong owner");
        let mut raw = circle();
        add_circle(&mut raw);
        raw.higher[0].boundary.pieces[0].term =
            alloc(&mut raw, Term::Constructor(ConstructorId::new(1)));
        rejects(&raw, "boundary point has wrong owner");
    }

    #[test]
    fn orphan_and_duplicate_members() {
        let mut raw = circle();
        raw.higher.push(HigherConstructorDecl {
            id: HigherConstructorId::new(1),
            inductive: InductiveId::new(0),
            name: "orphan".into(),
            arguments: vec![],
            dimensions: vec!["j".into()],
            result_indices: vec![],
            boundary: PartialConstructorBoundary::default(),
        });
        rejects(&raw, "orphan higher");
        let mut raw = circle();
        raw.families[0].constructors.remove(0);
        rejects(&raw, "orphan point");
        for member in [
            ConstructorRef::Point(ConstructorId::new(0)),
            ConstructorRef::Higher(HigherConstructorId::new(0)),
        ] {
            let mut raw = circle();
            raw.families[0].constructors.push(member);
            rejects(&raw, "duplicate membership");
        }
    }

    #[test]
    fn invalid_tags_cannot_supply_higher_membership() {
        let mut raw = circle();
        raw.families[0].constructors[1] = ConstructorRef::Point(ConstructorId::new(99));
        rejects(&raw, "missing point");
        let mut raw = circle();
        // Even the same numeric index in the other table cannot stand for loop.
        raw.families[0].constructors[1] = ConstructorRef::Point(ConstructorId::new(0));
        rejects(&raw, "duplicate membership");
        let mut raw = circle();
        raw.families[0].constructors[1] = ConstructorRef::Higher(HigherConstructorId::new(99));
        rejects(&raw, "missing higher");
        let mut raw = circle();
        raw.families[0].constructors.pop();
        rejects(&raw, "no higher constructor");
    }

    #[test]
    fn zero_dimensions_and_escaped_dimensions() {
        let mut raw = circle();
        raw.higher[0].dimensions.clear();
        rejects(&raw, "needs dimensions");
        let mut raw = circle();
        raw.higher[0].boundary.pieces[0].face =
            F::And(Box::new(F::Bot), Box::new(F::Eq(D::Bound(1), D::Zero)));
        // Impossible faces do not bypass structural validation.
        rejects(&raw, "escaped dimension");
    }

    #[test]
    fn face_syntax_is_cartesian_and_not_semantically_checked() {
        let mut raw = circle();
        raw.higher[0].dimensions.push("j".into());
        raw.higher[0].boundary.pieces[0].face = F::Or(
            Box::new(F::Top),
            Box::new(F::And(
                Box::new(F::Bot),
                Box::new(F::Eq(D::Bound(0), D::Bound(1))),
            )),
        );
        raw.validate().unwrap(); // Top's extra interior coverage is a Slice B error.
    }

    #[test]
    fn escaped_term_and_invalid_arena_ids() {
        let mut raw = circle();
        let escaped = alloc(&mut raw, Term::Var(0));
        raw.higher[0].arguments.push(entry("x", escaped));
        rejects(&raw, "escaped term");
        let mut raw = circle();
        raw.higher[0].boundary.pieces[0].term = TermId::new(usize::MAX);
        rejects(&raw, "invalid term ID");
        let mut raw = circle();
        let invalid = alloc(&mut raw, Term::Pi(TermId::new(999), TermId::new(999)));
        raw.points[0].arguments.push(entry("x", invalid));
        rejects(&raw, "invalid term ID");
    }

    #[test]
    fn all_referenced_ids_are_checked() {
        for term in [
            Term::Inductive(InductiveId::new(99)),
            Term::Constructor(ConstructorId::new(99)),
        ] {
            let mut raw = circle();
            let ty = alloc(&mut raw, term);
            raw.higher[0].arguments.push(entry("x", ty));
            rejects(&raw, "missing");
        }
    }

    #[test]
    fn result_index_arity_and_scope() {
        let mut raw = circle();
        let zero = alloc(&mut raw, Term::Zero);
        raw.higher[0].result_indices.push(zero);
        rejects(&raw, "result-index arity");
        let mut raw = parameterized();
        raw.higher[0].result_indices[0] = alloc(&mut raw, Term::Var(2));
        rejects(&raw, "escaped term");
    }

    #[test]
    fn later_point_boundary_is_rejected() {
        let mut raw = circle();
        raw.families[0].constructors.swap(0, 1);
        rejects(&raw, "declared earlier");
    }

    #[test]
    fn higher_and_self_references_have_no_term_encoding() {
        let mut raw = circle();
        // There is no Term variant accepting HigherConstructorId. Forging its
        // index as a point ID denotes base, not loop; another index is missing.
        raw.higher[0].boundary.pieces[0].term =
            alloc(&mut raw, Term::Constructor(ConstructorId::new(1)));
        rejects(&raw, "missing point");
        let mut raw = circle();
        raw.higher[0].boundary.pieces[0].term =
            alloc(&mut raw, Term::Inductive(InductiveId::new(0)));
        rejects(&raw, "earlier point application");
    }

    #[test]
    fn globals_and_executable_terms_are_forbidden() {
        let mut raw = circle();
        let global = alloc(&mut raw, Term::Global(0));
        raw.higher[0].arguments.push(entry("alias", global));
        rejects(&raw, "global alias");
        let mut raw = parameterized();
        let global = alloc(&mut raw, Term::Global(0));
        let base = raw.higher[0].boundary.pieces[0].term;
        raw.higher[0].boundary.pieces[0].term = alloc(&mut raw, Term::App(base, global));
        rejects(&raw, "application arity");
        let mut raw = circle();
        let base = raw.higher[0].boundary.pieces[0].term;
        let com = alloc(
            &mut raw,
            Term::Com {
                family: base,
                from: D::Zero,
                to: D::One,
                cap: base,
                tubes: vec![],
            },
        );
        raw.higher[0].boundary.pieces[0].term = com;
        rejects(&raw, "earlier point application");
        raw.higher[0].boundary.pieces[0].term = base;
        raw.higher[0].arguments.push(entry("bad", com));
        rejects(&raw, "unsupported metadata term");
    }

    #[test]
    fn direct_nested_and_negative_recursion_rejected_everywhere() {
        for position in 0..6 {
            let mut raw = circle();
            let current = alloc(&mut raw, Term::Inductive(InductiveId::new(0)));
            match position {
                0 => raw.families[0].parameters.push(entry("p", current)),
                1 => raw.families[0].indices.push(entry("n", current)),
                2 => raw.points[0].arguments.push(entry("x", current)),
                3 => raw.higher[0].arguments.push(entry("x", current)),
                _ => {
                    let nat = alloc(&mut raw, Term::Nat);
                    raw.families[0].indices.push(entry("n", nat));
                    raw.points[0]
                        .result_indices
                        .push(if position == 4 { current } else { nat });
                    raw.higher[0].result_indices.push(current);
                }
            }
            rejects(&raw, "current-family occurrence");
        }
        for negative in [false, true] {
            let mut raw = circle();
            let current = alloc(&mut raw, Term::Inductive(InductiveId::new(0)));
            let nat = alloc(&mut raw, Term::Nat);
            let ty = alloc(
                &mut raw,
                if negative {
                    Term::Pi(current, nat)
                } else {
                    Term::App(nat, current)
                },
            );
            raw.higher[0].arguments.push(entry("x", ty));
            rejects(&raw, "current-family occurrence");
        }
        let mut raw = circle();
        raw.points[0].recursive_arguments.push(0);
        rejects(&raw, "recursive annotations");
    }

    fn parameterized() -> RawHigherMetadata {
        let mut raw = circle();
        let universe = alloc(&mut raw, Term::U(0));
        let a = alloc(&mut raw, Term::Var(0));
        let parameter = alloc(&mut raw, Term::Var(1));
        raw.families[0].parameters.push(entry("A", universe));
        raw.families[0].indices.push(entry("index", a));
        raw.points[0].arguments.push(entry("x", a));
        raw.points[0].result_indices.push(a);
        raw.higher[0].arguments.push(entry("x", a));
        raw.higher[0].result_indices.push(a);
        let base = raw.higher[0].boundary.pieces[0].term;
        let applied = alloc(&mut raw, Term::App(base, parameter));
        let applied = alloc(&mut raw, Term::App(applied, a));
        for piece in &mut raw.higher[0].boundary.pieces {
            piece.term = applied;
        }
        raw
    }

    #[test]
    fn parameter_argument_and_index_telescope() {
        parameterized().validate().unwrap();
        let mut raw = parameterized();
        let base = alloc(&mut raw, Term::Constructor(ConstructorId::new(0)));
        let x = alloc(&mut raw, Term::Var(0));
        let wrong_parameter = alloc(&mut raw, Term::App(base, x));
        let applied = alloc(&mut raw, Term::App(wrong_parameter, x));
        raw.higher[0].boundary.pieces[0].term = applied;
        rejects(&raw, "uniform parameter");
    }

    #[test]
    fn boundary_fields_use_the_nonrecursive_whitelist() {
        for global in [false, true] {
            let mut raw = parameterized();
            let base = alloc(&mut raw, Term::Constructor(ConstructorId::new(0)));
            let parameter = alloc(&mut raw, Term::Var(1));
            let applied = alloc(&mut raw, Term::App(base, parameter));
            let field = if global {
                alloc(&mut raw, Term::Global(0))
            } else {
                base
            };
            let applied = alloc(&mut raw, Term::App(applied, field));
            raw.higher[0].boundary.pieces[0].term = applied;
            rejects(
                &raw,
                if global {
                    "global alias"
                } else {
                    "nested current-family"
                },
            );
        }
        let mut raw = parameterized();
        raw.higher[0].boundary.pieces[0].term =
            alloc(&mut raw, Term::Constructor(ConstructorId::new(0)));
        rejects(&raw, "application arity");
    }

    #[test]
    fn nested_binders_keep_term_and_dimension_namespaces_separate() {
        let mut raw = circle();
        let universe = alloc(&mut raw, Term::U(0));
        let var = alloc(&mut raw, Term::Var(0));
        let path = alloc(&mut raw, Term::Path(var, var, var));
        let pi = alloc(&mut raw, Term::Pi(universe, path));
        raw.higher[0].arguments.push(entry("f", pi));
        raw.validate().unwrap();
        // Path adds a dimension, not a term binder, so this is escaped.
        raw.higher[0].arguments[0].ty = path;
        rejects(&raw, "escaped term");
        // The initial grammar excludes dimension applications altogether,
        // including ones trying to access constructor dimensions in a domain.
        let app = alloc(&mut raw, Term::PApp(var, D::Bound(0)));
        raw.higher[0].arguments[0].ty = app;
        rejects(&raw, "unsupported metadata term");
    }

    #[test]
    fn incomplete_and_ill_typed_boundaries_wait_for_slice_b() {
        let mut raw = circle();
        raw.higher[0].boundary.pieces.truncate(1);
        raw.validate().unwrap(); // Slice B must reject missing i=1 perimeter.
        raw.higher[0].boundary.pieces.clear();
        raw.validate().unwrap(); // Empty boundary is structurally valid too.
        let mut raw = parameterized();
        let wrong_index = alloc(&mut raw, Term::U(0));
        raw.higher[0].result_indices[0] = wrong_index;
        raw.validate().unwrap(); // U 0 does not inhabit the arbitrary parameter A.
    }

    #[test]
    fn detects_forged_term_cycles_and_accepts_shared_dags() {
        let mut raw = circle();
        let predicted = TermId::new(raw.terms.len());
        let cyclic = alloc(&mut raw, Term::Suc(predicted));
        raw.higher[0].arguments.push(entry("bad", cyclic));
        rejects(&raw, "cyclic term graph");
        let mut raw = circle();
        let predicted = TermId::new(raw.terms.len());
        let base = raw.higher[0].boundary.pieces[0].term;
        raw.higher[0].boundary.pieces[0].term = alloc(&mut raw, Term::App(predicted, base));
        rejects(&raw, "cyclic boundary application");
        let mut raw = circle();
        let nat = alloc(&mut raw, Term::Nat);
        let shared = alloc(&mut raw, Term::Pi(nat, nat));
        raw.higher[0].arguments.push(entry("f", shared));
        raw.validate().unwrap();
    }

    #[test]
    fn concrete_dimension_and_piece_limits() {
        let mut raw = circle();
        raw.higher[0].dimensions = vec!["i".into(); MAX_DIMENSIONS];
        raw.validate().unwrap();
        raw.higher[0].dimensions.push("too_many".into());
        rejects(&raw, "dimension count budget");
        let mut raw = circle();
        let term = raw.higher[0].boundary.pieces[0].term;
        raw.higher[0].boundary.pieces = (0..MAX_PIECES_PER_CONSTRUCTOR)
            .map(|_| BoundaryPiece { face: F::Top, term })
            .collect();
        raw.validate().unwrap();
        raw.higher[0]
            .boundary
            .pieces
            .push(BoundaryPiece { face: F::Top, term });
        rejects(&raw, "boundary piece budget");
    }

    #[test]
    fn aggregate_piece_and_family_limits() {
        let mut raw = RawHigherMetadata::default();
        for _ in 0..=MAX_PIECES / MAX_PIECES_PER_CONSTRUCTOR {
            add_circle(&mut raw);
            let h = raw.higher.last_mut().unwrap();
            let term = h.boundary.pieces[0].term;
            h.boundary.pieces = (0..MAX_PIECES_PER_CONSTRUCTOR)
                .map(|_| BoundaryPiece { face: F::Top, term })
                .collect();
        }
        rejects(&raw, "aggregate boundary piece budget");
        let mut raw = RawHigherMetadata::default();
        for _ in 0..=MAX_FAMILIES {
            add_circle(&mut raw);
        }
        rejects(&raw, "family count budget");
    }

    #[test]
    fn bounded_stack_depth_and_shared_graph_work() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut raw = circle();
                let mut term = alloc(&mut raw, Term::Nat);
                for _ in 0..MAX_DEPTH {
                    term = alloc(&mut raw, Term::Suc(term));
                }
                raw.higher[0].arguments.push(entry("deep", term));
                raw.validate().unwrap();
                let deeper = alloc(&mut raw, Term::Suc(term));
                raw.higher[0].arguments[0].ty = deeper;
                rejects(&raw, "depth budget");
                let mut raw = circle();
                let mut face = F::Top;
                for _ in 0..=MAX_DEPTH {
                    face = F::And(Box::new(face), Box::new(F::Top));
                }
                raw.higher[0].boundary.pieces[0].face = face;
                rejects(&raw, "depth budget");
                let mut raw = circle();
                let mut term = alloc(&mut raw, Term::Nat);
                for _ in 0..18 {
                    term = alloc(&mut raw, Term::App(term, term));
                }
                raw.higher[0].arguments.push(entry("shared", term));
                rejects(&raw, "budget exhausted");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn aggregate_counters_fail_closed_at_the_limit() {
        let mut budget = Budget {
            work: MAX_WORK,
            ..Budget::default()
        };
        assert!(budget.work(1).is_err());
        let mut budget = Budget {
            terms: MAX_TERM_NODES,
            ..Budget::default()
        };
        assert!(budget.term(0).is_err());
        let mut budget = Budget {
            faces: MAX_FACE_NODES,
            ..Budget::default()
        };
        assert!(budget.face(0).is_err());
    }

    #[test]
    fn staged_family_dependencies_cannot_be_mutual() {
        let mut raw = circle();
        add_circle(&mut raw);
        let earlier = alloc(&mut raw, Term::Inductive(InductiveId::new(0)));
        raw.higher[1].arguments.push(entry("earlier", earlier));
        raw.validate().unwrap();
        let later = alloc(&mut raw, Term::Inductive(InductiveId::new(1)));
        raw.higher[0].arguments.push(entry("later", later));
        rejects(&raw, "forward family reference");
    }

    #[test]
    fn telescope_and_constructor_count_limits() {
        let mut raw = circle();
        let nat = alloc(&mut raw, Term::Nat);
        raw.higher[0].arguments = vec![entry("x", nat); MAX_TELESCOPE + 1];
        rejects(&raw, "telescope budget");
        let mut raw = circle();
        raw.points = vec![raw.points[0].clone(); MAX_CONSTRUCTORS];
        // Together with loop this exceeds the combined table budget; no IDs
        // are dereferenced and no certificate is returned.
        rejects(&raw, "constructor count budget");
    }

    #[test]
    fn boundary_field_depth_includes_its_application_spine() {
        let mut raw = parameterized();
        let base = alloc(&mut raw, Term::Constructor(ConstructorId::new(0)));
        let parameter = alloc(&mut raw, Term::Var(1));
        let applied = alloc(&mut raw, Term::App(base, parameter));
        let mut field = alloc(&mut raw, Term::Zero);
        for _ in 0..MAX_DEPTH {
            field = alloc(&mut raw, Term::Suc(field));
        }
        raw.higher[0].boundary.pieces[0].term = alloc(&mut raw, Term::App(applied, field));
        rejects(&raw, "depth budget");
    }

    #[test]
    fn invalid_boundary_argument_id_and_escaped_field_variable() {
        for invalid_id in [false, true] {
            let mut raw = parameterized();
            let base = alloc(&mut raw, Term::Constructor(ConstructorId::new(0)));
            let parameter = alloc(&mut raw, Term::Var(1));
            let applied = alloc(&mut raw, Term::App(base, parameter));
            let field = if invalid_id {
                TermId::new(999)
            } else {
                alloc(&mut raw, Term::Var(2))
            };
            raw.higher[0].boundary.pieces[0].term = alloc(&mut raw, Term::App(applied, field));
            rejects(
                &raw,
                if invalid_id {
                    "invalid term ID"
                } else {
                    "escaped term variable"
                },
            );
        }
    }
}
