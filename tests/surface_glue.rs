use kamo::{CheckedProgram, Options};

const LIBRARY: &str = include_str!("../examples/glue-surface.kamo");

fn check(extra: &str) -> kamo::Result<CheckedProgram> {
    CheckedProgram::check_surface(&format!("{LIBRARY}\n{extra}"))
}

#[test]
fn glue_paths_transport_and_elements_compute_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            LIBRARY,
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        for (name, expected) in [
            ("transported", "true"),
            ("projected", "true"),
            ("emptyProjected", "false"),
        ] {
            assert_eq!(program.normalize(name).unwrap().text, expected);
        }
    }
}

#[test]
fn glue_type_paths_have_the_declared_endpoints() {
    let program = check(
        r#"
        def left (A : Type) (B : Type) (e : Equiv A B) : Type = (ua A B e) @ 0
        def right (A : Type) (B : Type) (e : Equiv A B) : Type = (ua A B e) @ 1
    "#,
    )
    .unwrap();
    assert_eq!(
        program.normalize("left").unwrap().text,
        "(lam x0 (lam x1 (lam x2 x0)))"
    );
    assert_eq!(
        program.normalize("right").unwrap().text,
        "(lam x0 (lam x1 (lam x2 x1)))
"
        .trim()
    );
}

#[test]
fn glue_introductions_and_projections_synthesize_their_types() {
    let program = check(
        r#"
        def roundtrip : Bool = let v = glue G true { top => true }; let b = unglue G v; b
        def higher : Type1 = Glue Type {}
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("roundtrip").unwrap().text, "true");
}

#[test]
fn glue_domain_controls_element_coverage_without_requiring_total_faces() {
    check(
        r#"
        def local (A : Type) (x : A) : x == x =
          path i => unglue (Glue A { i = 0 => (A, idEquiv A) })
            (glue (Glue A { i = 0 => (A, idEquiv A) }) x { i = 0 => x })
    "#,
    )
    .unwrap();
    let error = check("def bad : G = glue G true {}").unwrap_err();
    assert!(
        error
            .message
            .contains("glue elements do not cover the Glue type's domain")
    );
    let error = check("def bad : emptyG = glue emptyG true { top => true }").unwrap_err();
    assert!(
        error
            .message
            .contains("glue element face exceeds the Glue type's domain")
    );
}

#[test]
fn glue_elements_must_map_to_their_base() {
    let error = check("def bad : G = glue G true { top => false }").unwrap_err();
    assert!(
        error
            .message
            .contains("glue element image disagrees with its base")
    );
}

#[test]
fn invalid_equivalences_types_and_scopes_are_rejected() {
    for extra in [
        "def bad : Type = Glue Bool { top => (Bool, true) }",
        "def bad : Type = Glue Bool { top => (Nat, idEquiv Bool) }",
        "def bad : Type = Glue true {}",
        "def bad : Type = Glue Bool { i = 0 => (Bool, idEquiv Bool) }",
        "def bad : Bool = unglue Bool true",
        "def bad : Bool = glue Bool true {}",
        "def bad : G = glue G zero { top => true }",
        "def bad : G = glue G true { top => zero }",
        "def bad : Bool = unglue G zero",
        "def bad : Type = Glue Bool { top => Bool }",
        "def bad : Type = Glue Bool { top => (Bool idEquiv Bool) }",
    ] {
        assert!(check(extra).is_err(), "{extra}");
    }
}

#[test]
fn overlapping_glue_data_must_have_equal_equivalence_witnesses() {
    let error = check(
        r#"
        def bad (A : Type) (B : Type) (e : Equiv A B) (f : Equiv A B) : Type =
          Glue B { top => (A, e); top => (A, f) }
    "#,
    )
    .unwrap_err();
    assert!(error.message.contains("Glue data disagree on an overlap"));
    check(
        r#"
        def good (A : Type) (B : Type) (e : Equiv A B) : Type =
          Glue B { top => (A, e); top => (A, e) }
    "#,
    )
    .unwrap();
}

#[test]
fn function_elements_receive_expected_types_from_named_glue_data() {
    let program = check(
        r#"
        def Functions : Type = Glue (Bool -> Bool) { top => (Bool -> Bool, idEquiv (Bool -> Bool)) }
        def function : Functions = glue Functions (\x => x) { top => \x => x }
        def answer : Bool = (unglue Functions function) true
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "true");
}

#[test]
fn equivalence_pairs_receive_the_kernel_equivalence_type_as_expected_type() {
    check(
        r#"
        def inline : Type = Glue Bool { top => (Bool,
          (\x => x, \b => ((b, path j => b), \h => path i =>
            (com (k => Bool) 1 0 b { i = 0 => b; i = 1 => (snd h) @ k },
             path j => com (k => Bool) 1 j b { i = 0 => b; i = 1 => (snd h) @ k }))))
        }
    "#,
    )
    .unwrap();
}

#[test]
fn face_scopes_and_compound_conditions_survive_dimension_shadowing() {
    check(
        r#"
        def constantType (A : Type) : A == A = path i => Glue A { i = 0 || i = 1 => (A, idEquiv A) }
        def typeSquare (A : Type) : (constantType A) == (constantType A) =
          path i => path i => Glue A { top && (i = 0 || i = 1) => (A, idEquiv A) }
    "#,
    )
    .unwrap();
}
