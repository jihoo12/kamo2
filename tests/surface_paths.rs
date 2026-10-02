use kamo::CheckedProgram;

const REFL: &str = r#"
    def refl (A : Type) (x : A) : x == x = path i => x
"#;

const CIRCLE: &str = r#"
    data Circle : Type where {
      base : Circle;
      loop : base == base
    }
"#;

#[test]
fn reflexivity_and_both_endpoints_compute() {
    let source = format!(
        r#"{REFL}
        def p : true == true = refl Bool true
        def left : Bool = p @ 0
        def right : Bool = p @ 1
    "#
    );
    let program = CheckedProgram::check_surface(&source).unwrap();
    for name in ["left", "right"] {
        assert_eq!(program.normalize(name).unwrap().text, "true");
    }
}

#[test]
fn neutral_paths_reduce_to_their_distinct_declared_endpoints() {
    let program = CheckedProgram::check_surface(
        r#"
        def left (p : true == false) : Bool = p @ 0
        def right (p : true == false) : Bool = p @ 1
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("left").unwrap().text, "(lam x0 true)");
    assert_eq!(program.normalize("right").unwrap().text, "(lam x0 false)");
}

#[test]
fn congruence_uses_bound_dimension_application() {
    let source = format!(
        r#"{REFL}
        def cong (A : Type) (B : Type) (f : A -> B)
          (x : A) (y : A) (p : x == y) : f x == f y =
          path i => f (p @ i)
        def id (x : Bool) : Bool = x
        def result : Bool = (cong Bool Bool id true true (refl Bool true)) @ 1
    "#
    );
    let program = CheckedProgram::check_surface(&source).unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn nested_dimension_shadowing_and_term_names_are_separate() {
    CheckedProgram::check_surface(
        r#"
        def square (A : Type) (x : A) (y : A) (p : x == y) : p == p =
          path i => path i => p @ i
        def sameName (A : Type) (i : A) : i == i = path i => i
    "#,
    )
    .unwrap();
}

#[test]
fn equality_family_does_not_capture_an_outer_dimension() {
    // q is neutral and may vary even though its endpoints agree. The inner
    // equality's function type mentions q @ i under its anonymous Path binder.
    CheckedProgram::check_surface(
        r#"
        def id (A : Type) (x : A) : A = x
        def families (A : Type) (q : A == A) :
          (id A == id A) == (id A == id A) =
          path i => id (q @ i) == id (q @ i)
    "#,
    )
    .unwrap();
}

#[test]
fn path_body_propagates_expected_types_to_match_lambda_and_let() {
    let source = format!(
        r#"{REFL}
        def id (x : Bool) : Bool = x
        def functions : id == id = path i => \x => let y = x; y
        def choose (b : Bool) : Bool = match b {{ true => true; false => false }}
        def matches (b : Bool) : choose b == choose b =
          path i => match b {{ true => true; false => false }}
        def viaLet (p : true == true) : true == true =
          path i => let x = p @ i; x
        def answer : Bool = (matches false) @ 0
        def proof (b : Bool) : b == b =
          match b {{ true => path i => true; false => path i => false }}
    "#
    );
    let program = CheckedProgram::check_surface(&source).unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "false");
}

#[test]
fn paths_reject_unknown_dimensions_wrong_types_and_wrong_boundaries() {
    for (source, message) in [
        (
            "def bad (p : true == true) : Bool = p @ missing",
            "unknown dimension",
        ),
        (
            "def bad (i : Bool) (p : true == true) : Bool = p @ i",
            "unknown dimension",
        ),
        ("def bad : true == zero = path i => true", "type mismatch"),
        ("def bad : true == false = path i => true", "path endpoint"),
        ("def bad : Bool = true @ 0", "expects a path"),
        (
            "def bad : Bool = let p = path i => true; true",
            "cannot infer a surface path abstraction",
        ),
    ] {
        let error = CheckedProgram::check_surface(source).unwrap_err();
        assert!(error.message.contains(message), "{source}: {error}");
    }
}

#[test]
fn surface_circle_path_constructor_checks_and_endpoints_compute() {
    let source = format!(
        r#"{CIRCLE}
        def p : base == base = loop
        def eta : base == base = path i => loop @ i
        def left : Circle = loop @ 0
        def right : Circle = loop @ 1
    "#
    );
    let program = CheckedProgram::check_surface(&source).unwrap();
    assert_eq!(program.normalize("left").unwrap().text, "base");
    assert_eq!(program.normalize("right").unwrap().text, "base");
    let path = program.normalize("p").unwrap().text;
    assert!(path.contains("higher loop"), "{path}");
    assert_eq!(program.normalize("eta").unwrap().text, path);
}

#[test]
fn surface_circle_match_remains_rejected_without_coherence_methods() {
    let source = format!(
        r#"{CIRCLE}
        def bad (x : Circle) : Circle =
          match x {{ base => base }}
    "#
    );
    let error = CheckedProgram::check_surface(&source).unwrap_err();
    assert!(error.message.contains("ordinary operation"), "{error}");
}

#[test]
fn surface_hit_classification_uses_constructor_results_only_and_stays_scoped() {
    CheckedProgram::check_surface("data Wrap : Type where { mk : (p : true == true) -> Wrap }")
        .unwrap();

    for source in [
        "data Bad (A : Type) : Type where { base : Bad A; loop : base == base }",
        "data Bad : Type where { base : Bad; loop : (x : Bool) -> base == base }",
        "data Bad : Type where { base : Bad; other : Bad; loop : base == base }",
        "data Bad : Type where { base : Bad; loop : true == true }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn shadowed_path_binder_preserves_outer_dimensions_in_local_types() {
    CheckedProgram::check_surface(
        r#"
        def use (T : Type) (k : (x : T) -> x == x) : Type = T
        def keep (A : Type) (q : A == A) : A == A =
          path i => use (q @ i) (\x => path i => let y = x; y)
    "#,
    )
    .unwrap();
}
