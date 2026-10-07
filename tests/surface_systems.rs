use kamo::{CheckedProgram, Options};

#[test]
fn compatible_path_systems_compute_endpoints_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/systems-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        for name in ["left", "right"] {
            assert_eq!(program.normalize(name).unwrap().text, "true");
        }
    }
}

#[test]
fn systems_synthesize_their_annotated_type_and_propagate_expected_types() {
    let program = CheckedProgram::check_surface(
        r#"
        def id : Bool -> Bool =
          let f = system (Bool -> Bool) { top => \x => x }; f
        def choose (b : Bool) : Bool = system Bool {
          top => match b { true => false; false => true }
        }
        def proof : true == true = system (true == true) { top => path i => true }
        def result : Bool = id (choose false)
        def types : Type = system Type { top => Bool }
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
    assert_eq!(program.normalize("types").unwrap().text, "Bool");
}

#[test]
fn dependent_system_types_are_instantiated_at_the_current_dimension() {
    CheckedProgram::check_surface(
        r#"
        def eta (A : Type) (B : Type) (p : A == B) (x : A) (y : B)
          (q : PathP (i => p @ i) x y) : PathP (i => p @ i) x y =
          path j => let z = system (p @ j) { top => q @ j }; z
    "#,
    )
    .unwrap();
}

#[test]
fn generic_interval_is_not_covered_by_its_two_endpoints() {
    let error = CheckedProgram::check_surface(
        r#"
        def bad : true == true = path i => system Bool {
          i = 0 => true; i = 1 => true
        }
    "#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("system faces do not cover the current face context")
    );
}

#[test]
fn overlaps_are_checked_under_their_faces() {
    for optimized in [false, true] {
        let options = Options {
            optimized,
            ..Default::default()
        };
        let error = CheckedProgram::check_surface_with(
            r#"
            def bad : Bool = system Bool { top => true; top => false }
        "#,
            options,
        )
        .unwrap_err();
        assert!(
            error
                .message
                .contains("system branches disagree on an overlap")
        );
        CheckedProgram::check_surface_with(
            r#"
            def good (p : true == false) : true == false =
              path i => system Bool { i = 0 => true; i = 1 => false; top => p @ i }
        "#,
            options,
        )
        .unwrap();
    }
}

#[test]
fn enclosing_face_context_controls_coverage_and_empty_systems() {
    CheckedProgram::check_surface(
        r#"
        def local (A : Type) (x : A) : x == x =
          path i => com (j => A) 0 0 x {
            i = 0 && i = 1 => system A {};
            i = 0 => system A { i = 0 => x }
          }
    "#,
    )
    .unwrap();
    for source in [
        "def bad : Bool = system Bool {}",
        "def bad : Bool = system Bool { bottom => true }",
        "def bad : Bool = system Bool { 0 = 1 => true }",
    ] {
        let error = CheckedProgram::check_surface(source).unwrap_err();
        assert!(
            error
                .message
                .contains("system faces do not cover the current face context")
        );
    }
}

#[test]
fn compound_faces_and_dimension_shadowing_preserve_system_scopes() {
    CheckedProgram::check_surface(
        r#"
        def constant (A : Type) (x : A) : x == x = path i => x
        def square (A : Type) (x : A) : (constant A x) == (constant A x) =
          path i => path i => system A { i = 0 || i = 1 => x; top => x }
        def diagonal (A : Type) (x : A) : (constant A x) == (constant A x) =
          path i => path j => system A { i = j && (i = 0 || j = 1) => x; top => x }
        def named (i : Bool) : i == i = path i => system Bool { top => i }
    "#,
    )
    .unwrap();
}

#[test]
fn invalid_systems_reject_type_scope_and_syntax_errors() {
    for source in [
        "def bad : Bool = system true { top => true }",
        "def bad : Bool = system Bool { top => zero }",
        "def bad : Nat = system Bool { top => true }",
        "def bad : Bool = system Bool { i = 0 => true }",
        "def bad : Bool = system Bool { 2 = 0 => true }",
        "def bad : Bool = system Bool { top => true bottom => true }",
        "def bad : Bool = system Bool { top => true",
        "def bad : Bool = system Bool { top == bottom => true }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}
