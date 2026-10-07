use kamo::{CheckedProgram, Options};

#[test]
fn nested_natural_and_indexed_vector_patterns_check_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/nested-patterns-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(program.normalize("result").unwrap().text, "(app suc zero)");
    }
}

#[test]
fn multiple_nested_columns_require_all_constructor_combinations() {
    let program = CheckedProgram::check_surface(
        r#"
        data Pair : Type where { pair : Bool -> Bool -> Pair }
        def same (p : Pair) : Bool = match p {
          pair (true) (true) => true;
          pair (true) (false) => false;
          pair (false) (true) => false;
          pair (false) (false) => true
        }
        def yes : Bool = same (pair true true)
        def no : Bool = same (pair true false)
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("yes").unwrap().text, "true");
    assert_eq!(program.normalize("no").unwrap().text, "false");
}

#[test]
fn dependent_expected_types_and_explicit_motives_refine_nested_scrutinees() {
    CheckedProgram::check_surface(
        r#"
        def witness (n : Nat) : Sigma (m : Nat) => m == n =
          match n return (value => Sigma (m : Nat) => m == value) {
            zero => (zero, path i => zero);
            suc (zero) => (suc zero, path i => suc zero);
            suc (suc k) => (suc (suc k), path i => suc (suc k))
          }
    "#,
    )
    .unwrap();
}

#[test]
fn nested_pattern_binders_shadow_outer_names_without_capture() {
    let program = CheckedProgram::check_surface(
        r#"
        def extract (k : Bool) (n : Nat) : Nat = match n {
          zero => zero;
          suc (zero) => zero;
          suc (suc k) => let x = k; x
        }
        def result : Nat = extract true (suc (suc (suc zero)))
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "(app suc zero)");
}

#[test]
fn missing_nested_cases_and_wrong_families_are_rejected() {
    for source in [
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (zero) => zero }",
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (true) => zero; suc (false) => zero }",
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (zero k) => zero; suc (suc k) => k }",
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (suc) => zero }",
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (missing) => zero }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn overlapping_rows_mixed_patterns_and_duplicate_binders_are_rejected() {
    for source in [
        "def bad (n : Nat) : Nat = match n { zero => zero; suc k => k; suc (zero) => zero }",
        "def bad (n : Nat) : Nat = match n { zero => zero; suc (zero) => zero; suc (zero) => zero; suc (suc k) => k }",
        "data Pair : Type where { pair : Nat -> Nat -> Pair } def bad (p : Pair) : Nat = match p { pair k (suc k) => k; pair x (zero) => x }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn self_recursion_is_not_reinterpreted_as_a_nested_eliminator_hypothesis() {
    let error = CheckedProgram::check_surface(
        r#"
        def bad (n : Nat) : Nat = match n {
          zero => zero; suc (zero) => zero; suc (suc k) => bad k
        }
    "#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("self recursion in nested-pattern matches")
    );
}

#[test]
fn deep_patterns_and_nested_binder_shadowing_survive_outer_match_substitution() {
    let program = CheckedProgram::check_surface(
        r#"
        def minusThree (n : Nat) : Nat = match n {
          zero => zero;
          suc (zero) => zero;
          suc (suc (zero)) => zero;
          suc (suc (suc k)) => k
        }
        def outer (n : Nat) : Nat = match n {
          zero => zero;
          suc k => match k { zero => zero; suc (zero) => zero; suc (suc k) => k }
        }
        def input : Nat = suc (suc (suc (suc zero)))
        def result : Nat = minusThree input
        def shadowResult : Nat = outer input
    "#,
    )
    .unwrap();
    for name in ["result", "shadowResult"] {
        assert_eq!(program.normalize(name).unwrap().text, "(app suc zero)");
    }
}
