use super::*;
use crate::eval::{Composition, Engine, Val};
use crate::face::Dim;
use crate::syntax::{D, Term, TermId};
use crate::{CheckedProgram, Options};

fn circle() -> Program {
    let raw = super::super::tests::circle();
    raw.validate()
        .unwrap()
        .validate_semantic()
        .unwrap()
        .publish()
        .unwrap()
}
fn app(p: &mut Program, d: D) -> TermId {
    p.alloc(
        Term::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![],
            arguments: vec![],
            dimensions: vec![d],
        },
        0,
    )
}
fn with_loop(mut p: Program) -> Program {
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let path = p.alloc(Term::Path(c, base, base), 0);
    let higher = app(&mut p, D::Bound(0));
    let body = p.alloc(Term::PLam(higher), 0);
    p.push_decl("loopPath".into(), path, body);
    p
}

#[test]
fn circle_path_checks_quotes_and_endpoints_compute_in_both_modes() {
    for optimized in [false, true] {
        let mut p = with_loop(circle());
        let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        for (name, d) in [("left", D::Zero), ("right", D::One)] {
            let loop_term = p.alloc(Term::Global(0), 0);
            let endpoint = p.alloc(Term::PApp(loop_term, d), 0);
            p.push_decl(name.into(), c, endpoint);
        }
        let checked = CheckedProgram::check_program(
            p,
            Options {
                optimized,
                ..Options::default()
            },
        )
        .unwrap();
        assert_eq!(
            checked
                .normalize_with(
                    "left",
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
            "base"
        );
        assert_eq!(
            checked
                .normalize_with(
                    "right",
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text,
            "base"
        );
        assert!(
            checked
                .normalize_with(
                    "loopPath",
                    Options {
                        optimized,
                        ..Options::default()
                    }
                )
                .unwrap()
                .text
                .contains("(higher loop () (i0))")
        );
    }
}

#[test]
fn dependent_circle_eliminator_checks_and_computes_in_both_modes() {
    for optimized in [false, true] {
        let mut p = circle();
        let circle = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);

        // P x = Path _ Circle x x. This motive genuinely depends on x.
        let x = p.alloc(Term::Var(0), 0);
        let refl_at_x = p.alloc(Term::Path(circle, x, x), 0);
        let motive = p.alloc(Term::Lam(refl_at_x), 0);

        // base_case = refl base.
        let base_case = p.alloc(Term::PLam(base), 0);

        // loop_case i = refl (loop @ i). Inside the nested path abstraction,
        // Bound(1) is the outer coherence dimension.
        let loop_at_i = app(&mut p, D::Bound(1));
        let refl_loop_at_i = p.alloc(Term::PLam(loop_at_i), 0);
        let loop_case = p.alloc(Term::PLam(refl_loop_at_i), 0);

        let result_at_base = p.alloc(Term::Path(circle, base, base), 0);
        let elim_base = p.alloc(
            Term::HitElim {
                inductive: InductiveId::new(0),
                parameters: vec![],
                motive,
                methods: vec![base_case, loop_case],
                indices: vec![],
                scrutinee: base,
            },
            0,
        );
        p.push_decl("elimBase".into(), result_at_base, elim_base);

        // The generic eliminator along loop has exactly the generated
        // dependent coherence type Path i (P (loop @ i)) base_case base_case.
        let loop_for_family = app(&mut p, D::Bound(0));
        let family_along_loop = p.alloc(Term::Path(circle, loop_for_family, loop_for_family), 0);
        let elim_loop_type = p.alloc(Term::Path(family_along_loop, base_case, base_case), 0);
        let loop_scrutinee = app(&mut p, D::Bound(0));
        let elim_loop_body = p.alloc(
            Term::HitElim {
                inductive: InductiveId::new(0),
                parameters: vec![],
                motive,
                methods: vec![base_case, loop_case],
                indices: vec![],
                scrutinee: loop_scrutinee,
            },
            0,
        );
        let elim_loop = p.alloc(Term::PLam(elim_loop_body), 0);
        p.push_decl("elimLoop".into(), elim_loop_type, elim_loop);

        let elim_loop_global = p.alloc(Term::Global(1), 0);
        let loop_left = p.alloc(Term::PApp(elim_loop_global, D::Zero), 0);
        p.push_decl("elimLoopLeft".into(), result_at_base, loop_left);
        let elim_loop_global = p.alloc(Term::Global(1), 0);
        let loop_right = p.alloc(Term::PApp(elim_loop_global, D::One), 0);
        p.push_decl("elimLoopRight".into(), result_at_base, loop_right);

        let checked = CheckedProgram::check_program(
            p,
            Options {
                optimized,
                ..Options::default()
            },
        )
        .unwrap();

        // Check the endpoint diamond explicitly. First reduce HitElim at a
        // generic loop point and only then restrict the result; compare that
        // with restricting the eliminator first, which exposes base and uses
        // point iota.
        {
            let mut e = Engine::new(&checked.program, optimized, 100_000, 100_000);
            let top = e.faces.top();
            let env = e.env(crate::eval::Env::default());
            let elim_loop = e.thunk(checked.program.decls[1].body, env);
            let elim_loop = e.force(elim_loop, top).unwrap();
            let Val::PLam(binder) = e.get(elim_loop) else {
                panic!("expected eliminator path");
            };
            let dimension = e.fresh_dim();
            let generic = e.inst_dim(&binder, Dim::Var(dimension));
            let higher_first = e.force(generic, top).unwrap();
            for endpoint in [Dim::Zero, Dim::One] {
                let higher_then_endpoint = e.restrict(higher_first, dimension, endpoint);
                let higher_then_endpoint = e.force(higher_then_endpoint, top).unwrap();
                let boundary_then_point = e.restrict(generic, dimension, endpoint);
                let boundary_then_point = e.force(boundary_then_point, top).unwrap();
                let ty = e.thunk(checked.program.decls[0].ty, env);
                assert!(
                    e.conv(higher_then_endpoint, boundary_then_point, Some(ty), top)
                        .unwrap()
                );
            }
        }

        let opts = Options {
            optimized,
            ..Options::default()
        };
        let base_text = checked.normalize_with("elimBase", opts).unwrap().text;
        assert_eq!(base_text, "(path i0 base)");
        let loop_text = checked.normalize_with("elimLoop", opts).unwrap().text;
        assert!(loop_text.contains("(higher loop () (i0))"), "{loop_text}");
        assert_eq!(
            checked.normalize_with("elimLoopLeft", opts).unwrap().text,
            base_text
        );
        assert_eq!(
            checked.normalize_with("elimLoopRight", opts).unwrap().text,
            base_text
        );
    }
}

#[test]
fn hit_eliminator_rejects_missing_and_noncoherent_methods() {
    for variant in 0..2 {
        let mut p = circle();
        let circle = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
        let nat = p.alloc(Term::Nat, 0);
        let motive = p.alloc(Term::Lam(nat), 0);
        let zero = p.alloc(Term::Zero, 0);
        let methods = if variant == 0 {
            vec![zero]
        } else {
            // The higher method must be a path coherence, not another point method.
            vec![zero, zero]
        };
        let elim = p.alloc(
            Term::HitElim {
                inductive: InductiveId::new(0),
                parameters: vec![],
                motive,
                methods,
                indices: vec![],
                scrutinee: base,
            },
            0,
        );
        p.push_decl("badHitElim".into(), nat, elim);
        let error = CheckedProgram::check_program(p, Options::default()).unwrap_err();
        assert!(
            error.message.contains(if variant == 0 {
                "wrong number of HIT eliminator methods"
            } else {
                "type mismatch"
            }),
            "{}",
            error.message
        );
        let _ = circle;
    }
}

#[test]
fn force_caches_faces_separately_and_conversion_splits_covers() {
    for optimized in [false, true] {
        let p = circle();
        let mut e = Engine::new(&p, optimized, 100_000, 100_000);
        let top = e.faces.top();
        let i = e.fresh_dim();
        let h = e.alloc(Val::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![],
            arguments: vec![],
            dimensions: vec![Dim::Var(i)],
        });
        let base = e.alloc(Val::Constructor(ConstructorId::new(0)));
        let ty = e.alloc(Val::Inductive(InductiveId::new(0)));
        assert!(matches!(
            {
                let forced = e.force(h, top).unwrap();
                e.get(forced)
            },
            Val::HigherApp { .. }
        ));
        let left = e.faces.eq(Dim::Var(i), Dim::Zero);
        let right = e.faces.eq(Dim::Var(i), Dim::One);
        let cover = e.faces.or(left, right);
        assert!(matches!(
            {
                let forced = e.force(h, cover).unwrap();
                e.get(forced)
            },
            Val::HigherApp { .. }
        ));
        assert!(e.conv(h, base, Some(ty), cover).unwrap());
        assert!(!e.conv(h, base, Some(ty), top).unwrap());
        assert!(matches!(
            {
                let forced = e.force(h, left).unwrap();
                e.get(forced)
            },
            Val::Constructor(_)
        ));
        assert!(matches!(
            {
                let forced = e.force(h, top).unwrap();
                e.get(forced)
            },
            Val::HigherApp { .. }
        ));
        let bot = e.faces.bot();
        assert!(e.conv(h, base, Some(ty), bot).unwrap());
    }
}

#[test]
fn renamed_and_endpoint_substitutions_reactivate_boundaries() {
    for optimized in [false, true] {
        let p = circle();
        let mut e = Engine::new(&p, optimized, 100_000, 100_000);
        let top = e.faces.top();
        let i = e.fresh_dim();
        let j = e.fresh_dim();
        let h = e.alloc(Val::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![],
            arguments: vec![],
            dimensions: vec![Dim::Var(i)],
        });
        let renamed = e.restrict(h, i, Dim::Var(j));
        let endpoint = e.restrict(renamed, j, Dim::One);
        let direct = e.restrict(h, i, Dim::One);
        let ty = e.alloc(Val::Inductive(InductiveId::new(0)));
        assert!(e.conv(endpoint, direct, Some(ty), top).unwrap());
        let at_j = e.faces.eq(Dim::Var(j), Dim::Zero);
        assert!(matches!(
            {
                let forced = e.force(renamed, at_j).unwrap();
                e.get(forced)
            },
            Val::Constructor(_)
        ));
        assert!(matches!(
            {
                let forced = e.force(h, at_j).unwrap();
                e.get(forced)
            },
            Val::HigherApp { .. }
        ));
        let other = e.alloc(Val::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![],
            arguments: vec![],
            dimensions: vec![Dim::Var(j)],
        });
        assert!(!e.conv(h, other, Some(ty), top).unwrap());
        let diagonal = e.faces.eq(Dim::Var(i), Dim::Var(j));
        assert!(e.conv(h, other, Some(ty), diagonal).unwrap());
    }
}

#[test]
fn ordinary_elimination_and_composition_never_treat_base_as_exhaustive() {
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let nat = p.alloc(Term::Nat, 0);
    let motive = p.alloc(Term::Lam(nat), 0);
    let zero = p.alloc(Term::Zero, 0);
    let elim = p.alloc(
        Term::Elim {
            inductive: InductiveId::new(0),
            parameters: vec![],
            motive,
            methods: vec![zero],
            indices: vec![],
            scrutinee: base,
        },
        0,
    );
    p.push_decl("bad".into(), nat, elim);
    let error = CheckedProgram::check_program(p, Options::default()).unwrap_err();
    assert!(error.message.contains("ordinary operation"));
    for optimized in [false, true] {
        let p = circle();
        let mut e = Engine::new(&p, optimized, 100_000, 100_000);
        let top = e.faces.top();
        let ty = e.alloc(Val::Inductive(InductiveId::new(0)));
        let base = e.alloc(Val::Constructor(ConstructorId::new(0)));
        let dim = e.fresh_dim();
        let com = e.alloc(Val::Com(Composition {
            dim,
            family: ty,
            from: Dim::Zero,
            to: Dim::One,
            cap: base,
            tubes: vec![],
        }));
        assert!(matches!(
            {
                let forced = e.force(com, top).unwrap();
                e.get(forced)
            },
            Val::Com(_)
        ));
        let bad = e.alloc(Val::Elim {
            inductive: InductiveId::new(0),
            parameters: vec![],
            motive: base,
            methods: vec![base],
            indices: vec![],
            scrutinee: base,
        });
        assert!(
            e.force(bad, top)
                .unwrap_err()
                .message
                .contains("ordinary operation")
        );
    }
    let _ = c;
}

#[test]
fn malformed_higher_applications_are_rejected() {
    for variant in 0..4 {
        let mut p = circle();
        let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        let t = p.alloc(
            Term::HigherApp {
                constructor: HigherConstructorId::new(if variant == 0 { 99 } else { 0 }),
                parameters: if variant == 1 { vec![c] } else { vec![] },
                arguments: vec![],
                dimensions: if variant == 2 {
                    vec![]
                } else if variant == 3 {
                    vec![D::Bound(0)]
                } else {
                    vec![D::Zero]
                },
            },
            0,
        );
        p.push_decl("bad".into(), c, t);
        assert!(CheckedProgram::check_program(p, Options::default()).is_err());
    }
}

#[test]
fn semantic_two_dimensional_signature_is_not_executable() {
    let mut raw = super::super::tests::circle();
    raw.higher[0].dimensions.push("j".into());
    let term = raw.higher[0].boundary.pieces[0].term;
    for endpoint in [D::Zero, D::One] {
        raw.higher[0].boundary.pieces.push(BoundaryPiece {
            face: F::Eq(D::Bound(1), endpoint),
            term,
        });
    }
    let structural = raw.validate().unwrap();
    let semantic = structural.validate_semantic().unwrap();
    assert!(
        semantic
            .publish()
            .unwrap_err()
            .message
            .contains("exactly one dimension")
    );
}

#[test]
fn forged_published_signature_must_revalidate_a_and_b() {
    let mut p = circle();
    p.higher[0].boundary.pieces.truncate(1);
    assert!(
        p.validate_inductives()
            .unwrap_err()
            .message
            .contains("incomplete perimeter")
    );
    let mut p = circle();
    p.higher[0].inductive = InductiveId::new(99);
    assert!(p.validate_inductives().is_err());
    let mut p = circle();
    p.inductives[0].constructors = FamilyConstructors::Ordinary(vec![ConstructorId::new(0)]);
    assert!(p.validate_inductives().is_err());
}

#[test]
fn surface_circle_stays_rejected() {
    assert!(
        CheckedProgram::check_surface(
            "data Circle : Type where\n  base : Circle\n  loop : base == base\n"
        )
        .is_err()
    );
}

fn indexed() -> Program {
    use crate::syntax::TelescopeEntry;
    let mut raw = super::super::tests::circle();
    let u = raw.terms.alloc(Node {
        term: Term::U(0),
        offset: 0,
    });
    let v0 = raw.terms.alloc(Node {
        term: Term::Var(0),
        offset: 0,
    });
    let v1 = raw.terms.alloc(Node {
        term: Term::Var(1),
        offset: 0,
    });
    let entry = |name: &str, ty| TelescopeEntry {
        name: name.into(),
        ty,
    };
    raw.families[0].parameters = vec![entry("A", u)];
    raw.families[0].indices = vec![entry("x", v0)];
    raw.points[0].arguments = vec![entry("x", v0)];
    raw.points[0].result_indices = vec![v0];
    raw.higher[0].arguments = vec![entry("x", v0)];
    raw.higher[0].result_indices = vec![v0];
    let head = raw.higher[0].boundary.pieces[0].term;
    let head = raw.terms.alloc(Node {
        term: Term::App(head, v1),
        offset: 0,
    });
    let body = raw.terms.alloc(Node {
        term: Term::App(head, v0),
        offset: 0,
    });
    for piece in &mut raw.higher[0].boundary.pieces {
        piece.term = body;
    }
    raw.validate()
        .unwrap()
        .validate_semantic()
        .unwrap()
        .publish()
        .unwrap()
}

fn parameterized_loop(mut p: Program) -> Program {
    let a = p.alloc(Term::Var(1), 0);
    let x = p.alloc(Term::Var(0), 0);
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let c = p.alloc(Term::App(c, a), 0);
    let c = p.alloc(Term::App(c, x), 0);
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let base = p.alloc(Term::App(base, a), 0);
    let base = p.alloc(Term::App(base, x), 0);
    let path = p.alloc(Term::Path(c, base, base), 0);
    let field = p.alloc(Term::Var(0), 0);
    let ty = p.alloc(Term::Pi(field, path), 0);
    let u = p.alloc(Term::U(0), 0);
    let ty = p.alloc(Term::Pi(u, ty), 0);
    let body = p.alloc(
        Term::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![a],
            arguments: vec![x],
            dimensions: vec![D::Bound(0)],
        },
        0,
    );
    let body = p.alloc(Term::PLam(body), 0);
    let body = p.alloc(Term::Lam(body), 0);
    let body = p.alloc(Term::Lam(body), 0);
    p.push_decl("indexedLoop".into(), ty, body);
    p
}

fn recheck_quotation(mut p: Program, optimized: bool) {
    p.validate_inductives().unwrap();
    let ty = p.decls[0].ty;
    let body = p.decls[0].body;
    let quoted = {
        let mut e = Engine::new(&p, optimized, 1_000_000, 250_000);
        e.check_declaration(0).unwrap();
        let env = e.env(crate::eval::Env::default());
        let face = e.faces.top();
        let ty = e.thunk(ty, env);
        let body = e.thunk(body, env);
        e.quote_core(body, ty, face).unwrap()
    };
    let root = quoted.append(&mut p).unwrap();
    p.push_decl("requote".into(), ty, root);
    let checked = CheckedProgram::check_program(
        p,
        Options {
            optimized,
            ..Options::default()
        },
    )
    .unwrap();
    let original = checked
        .normalize_with(
            &checked.program.decls[0].name,
            Options {
                optimized,
                ..Options::default()
            },
        )
        .unwrap()
        .text;
    let quoted = checked
        .normalize_with(
            "requote",
            Options {
                optimized,
                ..Options::default()
            },
        )
        .unwrap()
        .text;
    assert_eq!(original, quoted);
}

#[test]
fn structured_quotation_rechecks_circle_and_dependent_indexed_loops() {
    for optimized in [false, true] {
        recheck_quotation(with_loop(circle()), optimized);
        recheck_quotation(parameterized_loop(indexed()), optimized);
    }
}

#[test]
fn parameter_and_field_substitution_preserve_dependent_result_indices() {
    for optimized in [false, true] {
        let p = indexed();
        let mut e = Engine::new(&p, optimized, 100_000, 100_000);
        let top = e.faces.top();
        let i = e.fresh_dim();
        let bool_ty = e.alloc(Val::Bool);
        let tv = e.alloc(Val::True);
        let fv = e.alloc(Val::False);
        let x = e.variable(bool_ty);
        let Val::Var(level, _) = e.get(x) else {
            unreachable!()
        };
        let h = e.alloc(Val::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![bool_ty],
            arguments: vec![x],
            dimensions: vec![Dim::Var(i)],
        });
        let replaced = e.inst(
            &crate::eval::Binder {
                var: level,
                body: h,
            },
            tv,
        );
        let at = e.restrict(replaced, i, Dim::Zero);
        let base = e.alloc(Val::Constructor(ConstructorId::new(0)));
        let base = e.app(base, bool_ty);
        let base = e.app(base, tv);
        let ty = e
            .higher_result(HigherConstructorId::new(0), &[bool_ty], &[tv], &[Dim::Zero])
            .unwrap();
        assert!(e.conv(at, base, Some(ty), top).unwrap());
        let other = e.alloc(Val::HigherApp {
            constructor: HigherConstructorId::new(0),
            parameters: vec![bool_ty],
            arguments: vec![fv],
            dimensions: vec![Dim::Var(i)],
        });
        assert!(!e.conv(replaced, other, None, top).unwrap());
        let actual = e.neutral_type(replaced, top).unwrap();
        let expected = e
            .higher_result(
                HigherConstructorId::new(0),
                &[bool_ty],
                &[tv],
                &[Dim::Var(i)],
            )
            .unwrap();
        assert!(e.conv(actual, expected, None, top).unwrap());
    }
}

#[test]
fn nested_dimension_quotation_does_not_capture_outer_loop() {
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let outer = app(&mut p, D::Bound(0));
    let inner_ty = p.alloc(Term::Path(c, outer, outer), 0);
    let refl_base = p.alloc(Term::PLam(base), 0);
    let ty = p.alloc(Term::Path(inner_ty, refl_base, refl_base), 0);
    let inner = app(&mut p, D::Bound(1));
    let inner = p.alloc(Term::PLam(inner), 0);
    let body = p.alloc(Term::PLam(inner), 0);
    p.push_decl("nested".into(), ty, body);
    recheck_quotation(p, true);
}

#[test]
fn distinct_higher_heads_are_not_disjoint_at_the_boundary() {
    let mut raw = super::super::tests::circle();
    let mut second = raw.higher[0].clone();
    second.id = HigherConstructorId::new(1);
    second.name = "otherLoop".into();
    raw.families[0]
        .constructors
        .push(ConstructorRef::Higher(second.id));
    raw.higher.push(second);
    let p = raw
        .validate()
        .unwrap()
        .validate_semantic()
        .unwrap()
        .publish()
        .unwrap();
    for optimized in [false, true] {
        let mut e = Engine::new(&p, optimized, 100_000, 100_000);
        let top = e.faces.top();
        let i = e.fresh_dim();
        let mut make = |id| {
            e.alloc(Val::HigherApp {
                constructor: HigherConstructorId::new(id),
                parameters: vec![],
                arguments: vec![],
                dimensions: vec![Dim::Var(i)],
            })
        };
        let a = make(0);
        let b = make(1);
        let ty = e.alloc(Val::Inductive(InductiveId::new(0)));
        assert!(!e.conv(a, b, Some(ty), top).unwrap());
        let boundary = e.faces.eq(Dim::Var(i), Dim::Zero);
        assert!(e.conv(a, b, Some(ty), boundary).unwrap());
    }
}

#[test]
fn higher_arguments_reject_wrong_types_escaped_variables_and_invalid_ids() {
    for variant in 0..3 {
        let mut p = indexed();
        let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        let bool_ty = p.alloc(Term::Bool, 0);
        let tv = p.alloc(Term::True, 0);
        let c = p.alloc(Term::App(c, bool_ty), 0);
        let ty = p.alloc(Term::App(c, tv), 0);
        let argument = match variant {
            0 => p.alloc(Term::Zero, 0),
            1 => p.alloc(Term::Var(usize::MAX), 0),
            _ => TermId::new(usize::MAX),
        };
        let body = p.alloc(
            Term::HigherApp {
                constructor: HigherConstructorId::new(0),
                parameters: vec![bool_ty],
                arguments: vec![argument],
                dimensions: vec![D::Zero],
            },
            0,
        );
        p.push_decl("bad".into(), ty, body);
        assert!(CheckedProgram::check_program(p, Options::default()).is_err());
    }
}

#[test]
fn runtime_cycles_and_bot_face_scope_violations_fail_before_evaluation() {
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let id = TermId::new(p.terms.len());
    p.alloc(Term::App(id, id), 0);
    p.push_decl("cycle".into(), c, id);
    assert!(
        p.validate_inductives()
            .unwrap_err()
            .message
            .contains("cyclic executable")
    );
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let bad = app(&mut p, D::Bound(99));
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let body = p.alloc(Term::System(c, vec![(F::Top, base), (F::Bot, bad)]), 0);
    p.push_decl("bad".into(), c, body);
    assert!(
        p.validate_inductives()
            .unwrap_err()
            .message
            .contains("escaped executable dimension")
    );
}

#[test]
fn runtime_budgets_fail_without_partial_normal_forms() {
    let checked = CheckedProgram::check_program(with_loop(circle()), Options::default()).unwrap();
    for opts in [
        Options {
            fuel: 0,
            ..Options::default()
        },
        Options {
            max_nodes: 0,
            ..Options::default()
        },
    ] {
        assert!(checked.normalize_with("loopPath", opts).is_err());
    }
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let mut body = app(&mut p, D::Zero);
    for _ in 0..130 {
        body = p.alloc(Term::Ann(body, c), 0);
    }
    p.push_decl("deep".into(), c, body);
    assert!(
        p.validate_inductives()
            .unwrap_err()
            .message
            .contains("depth budget")
    );
}

#[test]
fn structured_quotation_preserves_glue_typed_higher_arguments() {
    for optimized in [false, true] {
        let mut p = indexed();
        let bool_ty = p.alloc(Term::Bool, 0);
        let g = p.alloc(Term::Glue(bool_ty, vec![]), 0);
        let x = p.alloc(Term::Var(0), 0);
        let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
        let c = p.alloc(Term::App(c, g), 0);
        let c = p.alloc(Term::App(c, x), 0);
        let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
        let base = p.alloc(Term::App(base, g), 0);
        let base = p.alloc(Term::App(base, x), 0);
        let path = p.alloc(Term::Path(c, base, base), 0);
        let ty = p.alloc(Term::Pi(g, path), 0);
        let h = p.alloc(
            Term::HigherApp {
                constructor: HigherConstructorId::new(0),
                parameters: vec![g],
                arguments: vec![x],
                dimensions: vec![D::Bound(0)],
            },
            0,
        );
        let body = p.alloc(Term::PLam(h), 0);
        let body = p.alloc(Term::Lam(body), 0);
        p.push_decl("glueLoop".into(), ty, body);
        recheck_quotation(p, optimized);
    }
}

#[test]
fn structured_quotation_preserves_blocked_higher_composition() {
    let mut p = circle();
    let c = p.alloc(Term::Inductive(InductiveId::new(0)), 0);
    let base = p.alloc(Term::Constructor(ConstructorId::new(0)), 0);
    let body = p.alloc(
        Term::Com {
            family: c,
            from: D::Zero,
            to: D::One,
            cap: base,
            tubes: vec![],
        },
        0,
    );
    p.push_decl("blocked".into(), c, body);
    recheck_quotation(p, true);
}

#[test]
fn higher_terms_cannot_bypass_validation_in_an_ordinary_program_on_bot() {
    let mut p = Program::default();
    let bool_ty = p.alloc(Term::Bool, 0);
    let tv = p.alloc(Term::True, 0);
    let bad = app(&mut p, D::Zero);
    let body = p.alloc(Term::System(bool_ty, vec![(F::Top, tv), (F::Bot, bad)]), 0);
    p.push_decl("bad".into(), bool_ty, body);
    assert!(CheckedProgram::check_program(p, Options::default()).is_err());

    let mut p = Program::default();
    let bool_ty = p.alloc(Term::Bool, 0);
    let tv = p.alloc(Term::True, 0);
    let forged = p.alloc(
        Term::HitElim {
            inductive: InductiveId::new(0),
            parameters: vec![],
            motive: bool_ty,
            methods: vec![],
            indices: vec![],
            scrutinee: tv,
        },
        0,
    );
    let body = p.alloc(
        Term::System(bool_ty, vec![(F::Top, tv), (F::Bot, forged)]),
        0,
    );
    p.push_decl("badHitElim".into(), bool_ty, body);
    assert!(CheckedProgram::check_program(p, Options::default()).is_err());
}
