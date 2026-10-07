use kamo::{CheckedProgram, Options};

#[test]
fn annotations_and_typed_lets_compute_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/annotations-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        for name in ["result", "packaged", "applied", "projected", "aliased"] {
            assert_eq!(program.normalize(name).unwrap().text, "true");
        }
    }
}

#[test]
fn name_ascriptions_do_not_change_dependent_function_binder_parsing() {
    let program = CheckedProgram::check_surface(
        r#"
        def id : (A : Type) -> (x : A) -> A = \A => \x => (x : A)
        def result : Bool = id (Bool : Type) (true : Bool)
        def cumulative : Type1 = (Bool : Type1)
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn annotations_check_the_value_even_when_used_only_in_a_type() {
    for source in [
        "def bad : Bool = (zero : Bool)",
        "def bad : Bool = let ignored : Bool = zero; true",
        "def bad : Bool = let ignored : true == false = path i => true; true",
        "def bad : Type = (true : Nat) == (true : Nat)",
        "def bad : Type = let A : Type = true; Bool",
        "def bad : Bool = (true : true)",
        "def bad : Bool = ((true : Nat) : Bool)",
        "def bad : Type = (Type : Type)",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn typed_pair_bindings_preserve_dependent_component_types() {
    CheckedProgram::check_surface(
        r#"
        def pack (A : Type) (x : A) : Sigma (y : A) => y == x =
          let p : Sigma (y : A) => y == x = (x, path i => x);
          (fst p, snd p)
        def local (A : Type) (x : A) : A =
          let f : (y : A) -> y == y = \y => path i => y;
          let p : x == x = f x; p @ 0
    "#,
    )
    .unwrap();
}

#[test]
fn function_and_path_aliases_supply_expected_types_and_support_application() {
    let program = CheckedProgram::check_surface(
        r#"
        def Function (A : Type) : Type = A -> A
        def Refl (A : Type) (x : A) : Type = x == x
        def value : Bool =
          let f : Function Bool = \x => let y = x; y;
          let p : Refl Bool true = path i => let x = true; x;
          let q = p @ 0; f q
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("value").unwrap().text, "true");
}

#[test]
fn annotation_types_preserve_outer_dimension_references() {
    CheckedProgram::check_surface(
        r#"
        def id (A : Type) (x : A) : A = x
        def ids (A : Type) (p : A == A) : PathP (i => p @ i -> p @ i) (id A) (id A) =
          path i => let f : p @ i -> p @ i = \x => x; f
        def sameName (i : Bool) : i == i = path i => (i : Bool)
    "#,
    )
    .unwrap();
}

#[test]
fn typed_lets_work_with_nested_patterns_without_explicit_motives() {
    let program = CheckedProgram::check_surface(
        r#"
        def minusTwo (n : Nat) : Nat =
          let result : Nat = match n {
            zero => zero; suc (zero) => zero; suc (suc k) => k
          }; result
        def answer : Nat = minusTwo (suc (suc (suc zero)))
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "(app suc zero)");
}

#[test]
fn invalid_annotation_and_typed_let_syntax_is_rejected() {
    for source in [
        "def bad : Bool = (true :)",
        "def bad : Bool = (true : Bool",
        "def bad : Bool = let x : = true; x",
        "def bad : Bool = let x : Bool true; x",
        "def bad : Bool = let x : Bool = true x",
        "def bad : Bool = true : Bool",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}
