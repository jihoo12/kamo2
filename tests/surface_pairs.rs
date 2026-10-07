use kamo::{CheckedProgram, Options};

#[test]
fn dependent_components_check_and_projections_compute_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            r#"
            def packed : Sigma (A : Type) => A = (Bool, true)
            def first : Type = fst packed
            def second : Bool = let x = snd packed; x
            def copy (p : Sigma (A : Type) => A) : Sigma (A : Type) => A = (fst p, snd p)
            def result : Bool = snd (copy packed)
        "#,
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(program.normalize("first").unwrap().text, "Bool");
        assert_eq!(program.normalize("second").unwrap().text, "true");
        assert_eq!(program.normalize("result").unwrap().text, "true");
    }
}

#[test]
fn named_dependent_pair_types_unfold_without_capturing_arguments() {
    let program = CheckedProgram::check_surface(
        r#"
        def Pack (A : Type) : Type = Sigma (x : A) => x == x
        def make (x : Bool) : Pack Bool = (x, path i => x)
        def proof (p : Pack Bool) : fst p == fst p = snd p
        def result : Bool = fst (make true)
        def shadow (x : Type) (y : x) : Pack x = (y, path i => y)
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn pair_components_receive_expected_lambda_match_and_path_types() {
    CheckedProgram::check_surface(r#"
        def functions : Sigma (f : Bool -> Bool) => f == f =
          (\x => x, path i => \x => x)
        def choice (b : Bool) : Sigma (x : Bool) => x == x =
          (match b { true => true; false => false }, path i => match b { true => true; false => false })
        def nested : Sigma (A : Type) => Sigma (x : A) => x == x =
          (Bool, (true, path i => true))
    "#).unwrap();
}

#[test]
fn dependent_pairs_inside_cubical_binders_preserve_dimension_scope() {
    CheckedProgram::check_surface(
        r#"
        def value (b : Bool) : Sigma (x : Bool) => Bool = (b, b)
        def line (A : Type) (p : A == A) :
          PathP (i => Sigma (B : Type) => Type) (A, A) (A, A) =
          path i => (p @ i, p @ i)
        def pairs : (value true) == (value true) =
          path i => system (Sigma (x : Bool) => Bool) { top => (true, true) }
    "#,
    )
    .unwrap();
}

#[test]
fn constructor_metadata_reconstructs_sigma_and_projection_types() {
    CheckedProgram::check_surface(
        r#"
        data Box : Type1 where { box : (p : Sigma (A : Type) => A) -> Box }
        def typeOf (b : Box) : Type = match b { box p => fst p }
    "#,
    )
    .unwrap();
}

#[test]
fn sigma_universes_are_the_maximum_of_component_levels() {
    CheckedProgram::check_surface(
        r#"
        def low : Type = Sigma (x : Bool) => Bool
        def high : Type1 = Sigma (A : Type) => A
        def higher : Type2 = Sigma (A : Type1) => A
    "#,
    )
    .unwrap();
    assert!(CheckedProgram::check_surface("def bad : Type = Sigma (A : Type) => A").is_err());
}

#[test]
fn invalid_pairs_and_projections_are_rejected() {
    for source in [
        "def bad : Sigma (A : Type) => A = (Bool, zero)",
        "def bad : Sigma (x : Bool) => x == x = (true, path i => false)",
        "def bad : Bool = (true, false)",
        "def bad : Bool = fst true",
        "def bad : Bool = snd true",
        "def bad : Bool = let p = (true, false); fst p",
        "def bad : Type = Sigma (x : true) => Bool",
        "def bad : Type = Sigma (x : Bool) => x",
        "def bad : Sigma (x : Bool) => Bool = (true,)",
        "def bad : Sigma (x : Bool) => Bool = (true, false, true)",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn identity_equivalence_witness_is_expressible_in_surface_syntax() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/pairs-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        for name in ["packedValue", "result", "identityResult"] {
            assert_eq!(program.normalize(name).unwrap().text, "true");
        }
    }
}
