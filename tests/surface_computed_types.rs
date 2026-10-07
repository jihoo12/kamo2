use kamo::{CheckedProgram, Options};

#[test]
fn let_computed_types_guide_functions_and_pairs() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            r#"
            def value : Bool =
              let f : (let A = Bool; A -> A) = \x => x;
              let p : (let A = Bool; Sigma (x : A) => A) = (false, f true);
              snd p
            def capture (A : Type) (x : A) : A =
              let f : (let B = A; (A : Type) -> B -> B) = \A => \y => y;
              f Bool x
            def shadow (A : Type) (x : A) : A =
              let f : (let A = Bool; A -> A) = \x => x; x
            "#,
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(program.normalize("value").unwrap().text, "true");
    }
}

#[test]
fn path_computed_types_guide_lambda_and_application() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            r#"
            def types : (Bool -> Bool) == (Bool -> Bool) = path i => Bool -> Bool
            def value : Bool = let f : types @ 0 = \x => x; f true
            def inline : Bool =
              let f : ((path i => Bool -> Bool : (Bool -> Bool) == (Bool -> Bool)) @ 1) = \x => x;
              f true
            "#,
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        for name in ["value", "inline"] {
            assert_eq!(program.normalize(name).unwrap().text, "true");
        }
    }
}

#[test]
fn neutral_computed_types_are_not_assumed_to_be_functions() {
    for source in [
        "def bad (p : Type == Type) : p @ 0 = \\x => x",
        "def bad : Bool = let f : (let A = Bool; A) = \\x => x; true",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn computed_type_reduction_does_not_bypass_kernel_validation() {
    for source in [
        "def bad : Bool = let f : (let A : Type = true; Bool -> Bool) = \\x => x; f true",
        "def bad : Bool = let f : ((path i => Bool -> Bool : Bool == Bool) @ 0) = \\x => x; f true",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}
