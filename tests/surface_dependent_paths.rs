use kamo::{CheckedProgram, Options};

const TRANSPORT_PATH: &str = r#"
def transport (A : Type) (B : Type) (p : A == B) (x : A) : B =
  coe (i => p @ i) 0 1 x

def transportPath (A : Type) (B : Type) (p : A == B) (x : A) :
  PathP (i => p @ i) x (transport A B p x) =
  path j => coe (i => p @ i) 0 j x
"#;

#[test]
fn dependent_transport_paths_check_and_endpoints_compute_in_both_modes() {
    for optimized in [false, true] {
        let source = format!(
            r#"{TRANSPORT_PATH}
            def left (A : Type) (B : Type) (p : A == B) (x : A) : A =
              let y = (transportPath A B p x) @ 0; y
            def right (A : Type) (B : Type) (p : A == B) (x : A) : B =
              let y = (transportPath A B p x) @ 1; y
            def refl : Bool == Bool = path i => Bool
            def result : Bool = right Bool Bool refl true
        "#
        );
        let program = CheckedProgram::check_surface_with(
            &source,
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            program.normalize("left").unwrap().text,
            "(lam x0 (lam x1 (lam x2 (lam x3 x3))))"
        );
        assert_eq!(program.normalize("result").unwrap().text, "true");
    }
}

#[test]
fn dependent_application_infers_the_type_at_a_generic_dimension() {
    let source = format!(
        r#"{TRANSPORT_PATH}
        def eta (A : Type) (B : Type) (p : A == B) (x : A)
          (q : PathP (i => p @ i) x (transport A B p x)) :
          PathP (j => p @ j) x (transport A B p x) =
          path i => let y = q @ i; y
    "#
    );
    CheckedProgram::check_surface(&source).unwrap();
}

#[test]
fn constant_dependent_paths_convert_to_homogeneous_equality() {
    let program = CheckedProgram::check_surface(
        r#"
        def explicit : PathP (i => Bool) true true = path j => true
        def ordinary : true == true = explicit
        def explicitAgain : PathP (i => Bool) true true = ordinary
        def result : Bool = explicitAgain @ 1
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn endpoints_supply_expected_function_types() {
    let program = CheckedProgram::check_surface(
        r#"
        def functions : PathP (i => Bool -> Bool) (\x => x) (\y => y) =
          path j => \z => z
        def answer : Bool = (functions @ 0) true
        def viaLet : PathP (i => Bool -> Bool) (\x => x) (\y => y) =
          path j => let f = functions @ j; \z => f z
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "true");
}

#[test]
fn family_binders_shadow_dimensions_without_capturing_endpoints() {
    CheckedProgram::check_surface(
        r#"
        def outer (A : Type) (q : A == A) : q == q =
          path i => PathP (i => q @ i) (q @ i) (q @ i)
    "#,
    )
    .expect_err("q @ i is a type, not an endpoint value of q @ 0");
    CheckedProgram::check_surface(
        r#"
        def refl (A : Type) (x : A) : PathP (i => A) x x = path i => x
        def square (A : Type) (x : A) : (refl A x) == (refl A x) =
          path i => path i => x
        def sameName (i : Bool) : PathP (i => Bool) i i = path i => i
    "#,
    )
    .unwrap();
}

#[test]
fn dependent_paths_reject_bad_families_endpoints_boundaries_and_scopes() {
    for source in [
        "def bad : PathP (0 => Bool) true true = path i => true",
        "def bad : PathP (i => true) true true = path i => true",
        "def bad : PathP (i => Bool) true zero = path i => true",
        "def bad : PathP (i => Bool) true false = path i => true",
        "def bad : PathP (i => Bool) true (true @ i) = path i => true",
        "def bad : PathP (i => Bool) true = path i => true",
        "def bad : PathP (i => Bool) true true = path j => true @ i",
        "def bad (A : Type) (B : Type) (p : A == B) (x : A) : PathP (i => p @ i) x x = path i => x",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn varying_function_families_propagate_expected_types_into_lambdas() {
    CheckedProgram::check_surface(
        r#"
        def ids (A : Type) (B : Type) (p : A == B) :
          PathP (i => p @ i -> p @ i) (\x => x) (\x => x) =
          path j => \x => let y = x; y
    "#,
    )
    .unwrap();
}

#[test]
fn endpoints_keep_the_outer_dimension_when_family_binders_shadow_it() {
    CheckedProgram::check_surface(
        r#"
        def squareTypes (A : Type) (q : A == A) : (A == A) == (A == A) =
          path i => PathP (i => Type) (q @ i) (q @ i)
    "#,
    )
    .unwrap();
}

#[test]
fn constructor_metadata_preserves_explicit_path_types_during_matching() {
    CheckedProgram::check_surface(
        r#"
        data Evidence (A : Type) (x : A) : Type where {
          wrap : (q : PathP (i => A) x x) -> Evidence A x
        }
        def endpoint (A : Type) (x : A) (e : Evidence A x) : A =
          match e { wrap q => let z = q @ 0; z }
    "#,
    )
    .unwrap();
}

#[test]
fn varying_paths_in_constructor_metadata_keep_the_existing_trust_boundary() {
    let error = CheckedProgram::check_surface(
        r#"
        data Evidence (A : Type) (B : Type) (p : A == B) (x : A) (y : B) : Type where {
          wrap : (q : PathP (i => p @ i) x y) -> Evidence A B p x y
        }
    "#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("unsupported term in inductive metadata")
    );
}
