//! Validation-only bridge to the existing kernel. This is a child of check so
//! Context, sort/check and typed conversion need no broader visibility.
//! Nothing here returns a Program, Engine, or semantic arena ID.
#![allow(dead_code)]

use super::Context;
use crate::arena::Key;
use crate::eval::{Engine, Env, Val};
use crate::face::Dim;
use crate::hit::{ConstructorRef, StructurallyCheckedHigherMetadata};
use crate::syntax::{InductiveDecl, Node, Program, Term, TermId};
use crate::{Error, Result};
use std::collections::HashSet;

#[derive(Clone, Copy)]
struct Limits {
    syntax_nodes: usize,
    higher: usize,
    pieces: usize,
    entailments: usize,
    pairs: usize,
    work: usize,
    fuel: u64,
    nodes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            syntax_nodes: 100_000,
            higher: 4096,
            pieces: 4096,
            entailments: 8192,
            pairs: 16_384,
            work: 200_000,
            fuel: 1_000_000,
            nodes: 250_000,
        }
    }
}

fn require(condition: bool, message: &str) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(Error::plain(format!("higher semantics: {message}")))
    }
}

fn charge(remaining: &mut usize, amount: usize, message: &str) -> Result<()> {
    *remaining = remaining
        .checked_sub(amount)
        .ok_or_else(|| Error::plain(format!("higher semantics: {message} budget exhausted")))?;
    Ok(())
}

fn bind_dimensions(
    engine: &mut Engine<'_>,
    mut context: Context,
    count: usize,
    work: &mut usize,
) -> Result<(Context, crate::face::FaceId)> {
    let mut perimeter = engine.faces.bot();
    for _ in 0..count {
        charge(work, 1, "aggregate semantic work")?;
        engine.tick()?;
        let (next, dimension) = engine.interval(&context);
        context = next;
        for endpoint in [Dim::Zero, Dim::One] {
            let facet = engine.faces.eq(Dim::Var(dimension), endpoint);
            perimeter = engine.faces.or(perimeter, facet);
        }
    }
    Ok((context, perimeter))
}

pub(crate) fn validate(checked: &StructurallyCheckedHigherMetadata<'_>) -> Result<()> {
    validate_with_limits(checked, Limits::default())
}

fn validate_with_limits(
    checked: &StructurallyCheckedHigherMetadata<'_>,
    mut limits: Limits,
) -> Result<()> {
    let raw = checked.raw();
    require(
        raw.terms.len() <= limits.syntax_nodes,
        "syntax arena budget exhausted",
    )?;

    // Preflight the entire aggregate quadratic workload before semantic work.
    for higher in &raw.higher {
        charge(&mut limits.higher, 1, "higher constructor")?;
        let n = higher.boundary.pieces.len();
        charge(&mut limits.pieces, n, "boundary piece")?;
        charge(&mut limits.entailments, 2, "coverage entailment")?;
        let pairs = n
            .checked_mul(n.saturating_sub(1))
            .and_then(|n| n.checked_div(2))
            .ok_or_else(|| Error::plain("higher semantics: overlap pair overflow"))?;
        charge(&mut limits.pairs, pairs, "overlap pair")?;
        charge(&mut limits.work, 3 + n + pairs, "aggregate semantic work")?;
    }

    // Preserve every TermId exactly. Copy only A-validated reachable nodes:
    // unused arena nodes may contain arbitrary unsupported syntax or deep faces.
    // Empty placeholders preserve positions without traversing/cloning that data.
    let mut pending = Vec::new();
    for family in &raw.families {
        pending.extend(
            family
                .parameters
                .iter()
                .chain(&family.indices)
                .map(|e| e.ty),
        );
    }
    for point in &raw.points {
        pending.extend(point.arguments.iter().map(|e| e.ty));
        pending.extend(&point.result_indices);
    }
    for higher in &raw.higher {
        pending.extend(higher.arguments.iter().map(|e| e.ty));
        pending.extend(&higher.result_indices);
        pending.extend(higher.boundary.pieces.iter().map(|p| p.term));
    }
    let mut reachable = HashSet::new();
    while let Some(id) = pending.pop() {
        charge(&mut limits.work, 1, "aggregate semantic work")?;
        if !reachable.insert(id) {
            continue;
        }
        require(id.index() < raw.terms.len(), "invalid term ID")?;
        match raw.terms.get(id).term {
            Term::Pi(a, b) | Term::Sigma(a, b) | Term::App(a, b) | Term::Ann(a, b) => {
                pending.extend([a, b]);
            }
            Term::Path(a, l, r) => pending.extend([a, l, r]),
            Term::Suc(a) => pending.push(a),
            Term::Var(_)
            | Term::U(_)
            | Term::Bool
            | Term::Nat
            | Term::True
            | Term::False
            | Term::Zero
            | Term::Inductive(_)
            | Term::Constructor(_) => {}
            _ => {
                return Err(Error::plain(
                    "higher semantics: unsupported validated syntax",
                ));
            }
        }
    }

    // This local view has point signatures only, no user declarations and no
    // higher terms. The A whitelist excludes Elim/Com/globals everywhere reachable.
    // Thus no elimination, exhaustiveness, or composition operation can observe
    // this deliberately incomplete membership. Never return or certify this view.
    let mut program = Program::default();
    for index in 0..raw.terms.len() {
        charge(&mut limits.work, 1, "aggregate semantic work")?;
        let id = TermId::new(index);
        program.terms.alloc(if reachable.contains(&id) {
            raw.terms.get(id).clone()
        } else {
            Node {
                term: Term::Zero,
                offset: 0,
            }
        });
    }
    for family in &raw.families {
        charge(
            &mut limits.work,
            1 + family.parameters.len() + family.indices.len(),
            "aggregate semantic work",
        )?;
        program.inductives.push(InductiveDecl {
            id: family.id,
            name: String::new(),
            universe: family.universe,
            parameters: family
                .parameters
                .iter()
                .map(|e| crate::syntax::TelescopeEntry {
                    name: String::new(),
                    ty: e.ty,
                })
                .collect(),
            indices: family
                .indices
                .iter()
                .map(|e| crate::syntax::TelescopeEntry {
                    name: String::new(),
                    ty: e.ty,
                })
                .collect(),
            constructors: crate::syntax::FamilyConstructors::Ordinary(
                family
                    .constructors
                    .iter()
                    .filter_map(|member| match member {
                        ConstructorRef::Point(id) => Some(*id),
                        ConstructorRef::Higher(_) => None,
                    })
                    .collect(),
            ),
        });
    }
    for point in &raw.points {
        charge(
            &mut limits.work,
            1 + point.arguments.len() + point.result_indices.len(),
            "aggregate semantic work",
        )?;
        program.constructors.push(crate::syntax::ConstructorDecl {
            id: point.id,
            inductive: point.inductive,
            name: String::new(),
            arguments: point
                .arguments
                .iter()
                .map(|e| crate::syntax::TelescopeEntry {
                    name: String::new(),
                    ty: e.ty,
                })
                .collect(),
            result_indices: point.result_indices.clone(),
            recursive_arguments: vec![],
        });
    }

    // One engine for the entire pass: fuel and node limits are aggregate, not
    // reset per constructor. Ordinary formation checks remain unchanged.
    let mut engine = Engine::new(&program, true, limits.fuel, limits.nodes);
    engine.check_inductive_declarations()?;
    engine.tick()?;
    for higher in &raw.higher {
        let family = program
            .inductives
            .get(higher.inductive.index())
            .ok_or_else(|| Error::plain("higher semantics: missing owner"))?;
        let env = engine.env(Env::default());
        let mut context = Context {
            env,
            types: vec![],
            face: engine.faces.top(),
        };
        let mut parameters = Vec::new();
        for entry in &family.parameters {
            charge(&mut limits.work, 1, "aggregate semantic work")?;
            engine.tick()?;
            let ty = engine.thunk(entry.ty, context.env);
            let (next, value) = engine.extend(&context, ty);
            context = next;
            parameters.push(value);
        }
        for entry in &higher.arguments {
            charge(&mut limits.work, 1, "aggregate semantic work")?;
            let level = engine.sort(entry.ty, &context)?;
            require(
                level <= family.universe,
                "higher field above family universe",
            )?;
            let ty = engine.thunk(entry.ty, context.env);
            context = engine.extend(&context, ty).0;
        }

        let (context, perimeter) = bind_dimensions(
            &mut engine,
            context,
            higher.dimensions.len(),
            &mut limits.work,
        )?;
        let mut result = engine.alloc(Val::Inductive(family.id));
        for value in &parameters {
            result = engine.app(result, *value);
        }
        let mut index_env = engine.env(Env {
            terms: parameters,
            dims: vec![],
        });
        for (entry, index) in family.indices.iter().zip(&higher.result_indices) {
            charge(&mut limits.work, 1, "aggregate semantic work")?;
            let ty = engine.thunk(entry.ty, index_env);
            engine.check(*index, ty, &context)?;
            let value = engine.thunk(*index, context.env);
            result = engine.app(result, value);
            let mut next = engine.environment(index_env);
            next.terms.push(value);
            index_env = engine.env(next);
        }

        let mut coverage = engine.faces.bot();
        let mut pieces = Vec::new();
        for piece in &higher.boundary.pieces {
            // A bounds face recursion depth and aggregate face nodes.
            let face = engine.face(&piece.face, context.env);
            engine.tick()?;
            coverage = engine.faces.or(coverage, face);
            let under = engine.faces.and(context.face, face);
            engine
                .check(
                    piece.term,
                    result,
                    &Context {
                        face: under,
                        ..context.clone()
                    },
                )
                .map_err(|mut error| {
                    error.message = format!("higher boundary typing: {}", error.message);
                    error
                })?;
            let value = engine.thunk(piece.term, context.env);
            pieces.push((under, value));
        }
        engine.tick()?;
        require(
            engine.faces.entails(perimeter, coverage)?,
            "incomplete perimeter coverage",
        )?;
        require(
            engine.faces.entails(coverage, perimeter)?,
            "extra interior coverage",
        )?;
        for (position, &(face, value)) in pieces.iter().enumerate() {
            for &(other_face, other_value) in &pieces[..position] {
                engine.tick()?;
                let overlap = engine.faces.and(face, other_face);
                require(
                    engine.conv(value, other_value, Some(result), overlap)?,
                    "boundary overlap disagreement",
                )?;
            }
        }
        // Allocation errors cannot be hidden by a final successful conversion.
        engine.tick()?;
    }
    engine.tick()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hit::{
        BoundaryPiece, HigherConstructorDecl, HigherConstructorId, HigherFamilyDecl,
        PartialConstructorBoundary, RawHigherMetadata,
    };
    use crate::syntax::{ConstructorDecl, ConstructorId, D, F, InductiveId};

    fn fixture() -> RawHigherMetadata {
        let mut raw = RawHigherMetadata::default();
        let owner = InductiveId::new(0);
        let point = ConstructorId::new(0);
        let higher = HigherConstructorId::new(0);
        let term = raw.terms.alloc(Node {
            term: Term::Constructor(point),
            offset: 0,
        });
        raw.families.push(HigherFamilyDecl {
            id: owner,
            name: "BudgetCircle".into(),
            universe: 0,
            parameters: vec![],
            indices: vec![],
            constructors: vec![ConstructorRef::Point(point), ConstructorRef::Higher(higher)],
        });
        raw.points.push(ConstructorDecl {
            id: point,
            inductive: owner,
            name: "base".into(),
            arguments: vec![],
            result_indices: vec![],
            recursive_arguments: vec![],
        });
        raw.higher.push(HigherConstructorDecl {
            id: higher,
            inductive: owner,
            name: "loop".into(),
            arguments: vec![],
            dimensions: vec!["i".into()],
            result_indices: vec![],
            boundary: PartialConstructorBoundary {
                pieces: [D::Zero, D::One]
                    .into_iter()
                    .map(|endpoint| BoundaryPiece {
                        face: F::Eq(D::Bound(0), endpoint),
                        term,
                    })
                    .collect(),
            },
        });
        raw
    }

    fn rejects(raw: &RawHigherMetadata, limits: Limits, message: &str) {
        let checked = raw.validate().expect("structural certificate");
        let error = validate_with_limits(&checked, limits).unwrap_err();
        assert!(
            error.message.contains(message),
            "expected {message:?}, got {error}"
        );
    }

    #[test]
    fn independent_semantic_resource_caps_fail_closed() {
        let raw = fixture();
        for (limits, message) in [
            (
                Limits {
                    syntax_nodes: 0,
                    ..Limits::default()
                },
                "syntax arena",
            ),
            (
                Limits {
                    higher: 0,
                    ..Limits::default()
                },
                "higher constructor",
            ),
            (
                Limits {
                    pieces: 1,
                    ..Limits::default()
                },
                "boundary piece",
            ),
            (
                Limits {
                    entailments: 1,
                    ..Limits::default()
                },
                "coverage entailment",
            ),
            (
                Limits {
                    pairs: 0,
                    ..Limits::default()
                },
                "overlap pair",
            ),
            (
                Limits {
                    work: 0,
                    ..Limits::default()
                },
                "aggregate semantic work",
            ),
            (
                Limits {
                    fuel: 0,
                    ..Limits::default()
                },
                "evaluation budget",
            ),
            (
                Limits {
                    nodes: 0,
                    ..Limits::default()
                },
                "arena node budget",
            ),
        ] {
            rejects(&raw, limits, message);
        }
    }

    #[test]
    fn aggregate_pairs_are_bounded_across_constructors() {
        let mut raw = fixture();
        let term = raw.higher[0].boundary.pieces[0].term;
        for _ in 2..129 {
            raw.higher[0].boundary.pieces.push(BoundaryPiece {
                face: F::Eq(D::Bound(0), D::Zero),
                term,
            });
        }
        // 8,256 pairs is permitted by the default 16,384 aggregate cap.
        raw.validate().unwrap().validate_semantic().unwrap();
        let second = HigherConstructorId::new(1);
        raw.families[0]
            .constructors
            .push(ConstructorRef::Higher(second));
        raw.higher.push(HigherConstructorDecl {
            id: second,
            inductive: InductiveId::new(0),
            name: "other".into(),
            arguments: vec![],
            dimensions: vec!["j".into()],
            result_indices: vec![],
            boundary: PartialConstructorBoundary {
                pieces: raw.higher[0]
                    .boundary
                    .pieces
                    .iter()
                    .map(|p| BoundaryPiece {
                        face: p.face.clone(),
                        term: p.term,
                    })
                    .collect(),
            },
        });
        // Each constructor fits individually; together 16,512 pairs do not.
        rejects(&raw, Limits::default(), "overlap pair");
    }

    #[test]
    fn generic_dimensions_preserve_de_bruijn_order_and_non_boolean_extent() {
        let program = Program::default();
        let mut engine = Engine::new(&program, true, 1000, 1000);
        let env = engine.env(Env::default());
        let context = Context {
            env,
            types: vec![],
            face: engine.faces.top(),
        };
        let mut work = 10;
        let (context, perimeter) = bind_dimensions(&mut engine, context, 2, &mut work).unwrap();
        let dims = engine.environment(context.env).dims;
        assert_eq!(dims.len(), 2);
        assert_ne!(dims[0], dims[1]);
        assert!(dims.iter().all(|d| matches!(d, Dim::Var(_))));
        assert_eq!(engine.dim(D::Bound(0), context.env), dims[1]);
        assert_eq!(engine.dim(D::Bound(1), context.env), dims[0]);
        let first_zero = engine.face(&F::Eq(D::Bound(1), D::Zero), context.env);
        let second_zero = engine.face(&F::Eq(D::Bound(0), D::Zero), context.env);
        assert!(!engine.faces.entails(first_zero, second_zero).unwrap());
        let corner = engine.faces.and(first_zero, second_zero);
        assert!(!engine.faces.inconsistent(corner).unwrap());
        assert!(engine.faces.entails(corner, perimeter).unwrap());
        let top = engine.faces.top();
        assert!(!engine.faces.entails(top, perimeter).unwrap());
    }

    #[test]
    fn face_solver_exhaustion_is_propagated() {
        let mut raw = fixture();
        raw.higher[0].dimensions = (0..14).map(|i| format!("i{i}")).collect();
        // Two 128-clause operands overflow the 4,096-product limit before
        // constructing a large DNF, keeping this adversarial test small/fast.
        let half = |start| {
            (start..start + 7).fold(F::Top, |face, i| {
                F::And(
                    Box::new(face),
                    Box::new(F::Or(
                        Box::new(F::Eq(D::Bound(i), D::Zero)),
                        Box::new(F::Eq(D::Bound(i), D::One)),
                    )),
                )
            })
        };
        raw.higher[0].boundary.pieces[0].face = F::And(Box::new(half(0)), Box::new(half(7)));
        rejects(&raw, Limits::default(), "face solver expansion budget");
    }

    #[test]
    fn unreachable_unvalidated_syntax_is_not_copied_or_executed() {
        let mut raw = fixture();
        let forged = TermId::new(usize::MAX);
        raw.terms.alloc(Node {
            term: Term::Com {
                family: forged,
                from: D::Bound(999),
                to: D::One,
                cap: forged,
                tubes: vec![(F::Top, forged)],
            },
            offset: 0,
        });
        raw.validate().unwrap().validate_semantic().unwrap();
    }

    #[test]
    fn reachable_sparse_arena_ids_are_preserved() {
        let mut raw = fixture();
        for _ in 0..20 {
            raw.terms.alloc(Node {
                term: Term::Global(999),
                offset: 0,
            });
        }
        let term = raw.terms.alloc(Node {
            term: Term::Constructor(ConstructorId::new(0)),
            offset: 0,
        });
        for piece in &mut raw.higher[0].boundary.pieces {
            piece.term = term;
        }
        raw.validate().unwrap().validate_semantic().unwrap();
    }
}
