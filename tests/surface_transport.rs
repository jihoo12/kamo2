use kamo::CheckedProgram;

#[test]
fn transport_computes_in_constant_families_and_in_both_directions() {
    let program = CheckedProgram::check_surface(
        r#"
        def transport (A : Type) (B : Type) (p : A == B) (x : A) : B =
          coe (i => p @ i) 0 1 x
        def back (A : Type) (B : Type) (p : A == B) (x : B) : A =
          coe (i => p @ i) 1 0 x
        def refl (A : Type) : A == A = path i => A
        def forward : Bool = transport Bool Bool (refl Bool) true
        def backward : Bool = back Bool Bool (refl Bool) false
        def direct : Bool = coe (i => Bool) 0 1 true
        "#,
    )
    .unwrap();
    for (name, expected) in [
        ("forward", "true"),
        ("backward", "false"),
        ("direct", "true"),
    ] {
        assert_eq!(program.normalize(name).unwrap().text, expected);
    }
}

#[test]
fn transported_values_infer_destination_types_in_let_bindings() {
    CheckedProgram::check_surface(
        r#"
        def transport (A : Type) (B : Type) (p : A == B) (x : A) : B =
          let y = coe (i => p @ i) 0 1 x; y
        def apply (A : Type) (B : Type) (p : A == B)
          (f : A -> A) (x : B) : B =
          (coe (i => p @ i -> p @ i) 0 1 f) x
        "#,
    )
    .unwrap();
}

#[test]
fn source_type_guides_lambda_and_match_caps() {
    let program = CheckedProgram::check_surface(
        r#"
        def id : Bool -> Bool = coe (i => Bool -> Bool) 0 1 (\x => x)
        def choose (b : Bool) : Bool =
          coe (i => Bool) 0 1 (match b { true => false; false => true })
        def result : Bool = id (choose false)
        "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn family_binder_does_not_scope_over_endpoints_or_cap() {
    let program = CheckedProgram::check_surface(
        r#"
        def same (A : Type) (x : A) : x == x =
          path i => coe (i => A) i i x
        def outer (A : Type) (p : A == A) : p == p =
          path i => path j => coe (i => Type) 0 0 (p @ j)
        def termName (i : Bool) : Bool = coe (i => Bool) 0 0 i
        "#,
    )
    .unwrap();
    assert_eq!(program.normalize("termName").unwrap().text, "(lam x0 x0)");
}

#[test]
fn nested_transport_preserves_outer_dimension_references() {
    CheckedProgram::check_surface(
        r#"
        def nested (A : Type) (p : A == A) (x : A) : x == x =
          path i => coe (j => A) i i (coe (i => A) j j x)
        "#,
    )
    .expect_err("the inner coe cannot refer to the outer family's bound j in its cap");
    CheckedProgram::check_surface(
        r#"
        def nested (A : Type) (x : A) : x == x =
          path i => coe (j => A) i i (coe (i => A) 0 0 x)
        "#,
    )
    .unwrap();
}

#[test]
fn invalid_transport_is_rejected_by_parser_elaborator_or_kernel() {
    for source in [
        "def bad : Bool = coe (0 => Bool) 0 1 true",
        "def bad : Bool = coe (i => Bool) 0 2 true",
        "def bad : Bool = coe (i => Bool) 0 i true",
        "def bad : Bool = coe (i => true) 0 1 true",
        "def bad : Bool = coe (i => Bool) 0 1 zero",
        "def bad : Nat = coe (i => Bool) 0 1 true",
        "def bad : Bool = coe (i => Bool) 0 1",
        "def bad : Bool = coe (i => Bool) 0 1 (true @ i)",
        "def bad (A : Type) (B : Type) (p : A == B) (x : B) : B = coe (i => p @ i) 0 1 x",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn neutral_type_lines_remain_transport_and_same_endpoints_compute() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            r#"
            def move (A : Type) (p : A == A) (x : A) : A =
              coe (i => p @ i) 0 1 x
            def stay (A : Type) (p : A == A) (x : A) : A =
              coe (i => p @ i) 0 0 x
            def line (A : Type) (p : A == A) : p == p =
              path i => path j => coe (j => Type) i i (p @ j)
            "#,
            kamo::Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            program.normalize("stay").unwrap().text,
            "(lam x0 (lam x1 (lam x2 x2)))"
        );
        assert!(program.normalize("move").unwrap().text.contains("com"));
    }
}
