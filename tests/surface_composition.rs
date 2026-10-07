use kamo::{CheckedProgram, Options};

#[test]
fn cartesian_path_concat_and_inverse_check_in_both_evaluators() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/composition-surface.kamo"),
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
fn full_face_selects_the_tube_and_empty_tubes_match_transport() {
    let program = CheckedProgram::check_surface(
        r#"
        def selected : Bool = com (i => Bool) 0 1 true { top => true }
        def empty : Bool = com (i => Bool) 0 1 false {}
        def compound : Bool = com (i => Bool) 0 1 true {
          (0=0 && 0=1) || 1=1 => true
        }
    "#,
    )
    .unwrap();
    for (name, expected) in [
        ("selected", "true"),
        ("empty", "false"),
        ("compound", "true"),
    ] {
        assert_eq!(program.normalize(name).unwrap().text, expected);
    }
}

#[test]
fn destination_type_is_inferred_for_varying_families() {
    CheckedProgram::check_surface(
        r#"
        def move (A : Type) (B : Type) (p : A == B) (x : A) : B =
          let result = com (i => p @ i) 0 1 x {}; result
        def eta (A : Type) (B : Type) (p : A == B) (x : A)
          (y : B) (q : PathP (i => p @ i) x y) : y == y =
          path k => com (i => p @ i) 0 1 x {
            k = 0 || k = 1 => q @ i
          }
    "#,
    )
    .unwrap();
}

#[test]
fn expected_types_reach_lambda_match_and_path_tubes() {
    CheckedProgram::check_surface(
        r#"
        def functions : Bool -> Bool =
          com (i => Bool -> Bool) 0 1 (\x => x) { top => \x => x }
        def choose (b : Bool) : Bool =
          com (i => Bool) 0 1 (match b { true => true; false => false }) {
            top => match b { true => true; false => false }
          }
        def paths : true == true =
          com (i => true == true) 0 1 (path j => true) { top => path j => true }
    "#,
    )
    .unwrap();
}

#[test]
fn outer_dimensions_are_renamed_in_faces_and_shadowed_in_tube_bodies() {
    CheckedProgram::check_surface(
        r#"
        def shadow (A : Type) (x : A) (p : x == x) : x == x =
          path i => com (i => A) 0 1 x { i = 0 || i = 1 => p @ i }
        def nested (A : Type) (x : A) : x == x =
          path i => com (j => A) i i x {
            i = 0 => com (i => A) 0 0 x { j = 0 || j = 1 => x }
          }
    "#,
    )
    .unwrap();
}

#[test]
fn diagonal_faces_and_intersections_remain_cartesian_cofibrations() {
    CheckedProgram::check_surface(
        r#"
        def pathValue (A : Type) (x : A) : x == x = path i => x
        def square (A : Type) (x : A) : (pathValue A x) == (pathValue A x) =
          path i => path j => com (k => A) 0 0 x {
            i = j && (i = 0 || j = 1) => x
          }
    "#,
    )
    .unwrap();
}

#[test]
fn invalid_compositions_reject_bad_faces_scopes_and_boundary_data() {
    for source in [
        "def bad : Bool = com (i => Bool) 0 1 true { top => false }",
        "def bad : Bool = com (i => Bool) 0 1 true { top => zero }",
        "def bad : Bool = com (i => Bool) 0 1 true { i = 0 => true }",
        "def bad : Bool = com (i => Bool) 0 1 (true @ i) {}",
        "def bad : Bool = com (0 => Bool) 0 1 true {}",
        "def bad : Bool = com (i => Bool) 0 2 true {}",
        "def bad : Bool = com (i => true) 0 1 true {}",
        "def bad : Bool = com (i => Bool) 0 1 true { 2 = 0 => true }",
        "def bad : Bool = com (i => Bool) 0 1 true { top & bottom => true }",
        "def bad : Bool = com (i => Bool) 0 1 true { top == bottom => true }",
        "def bad : Bool = com (i => Bool) 0 1 true { top => true bottom => true }",
        "def bad : Bool = com (i => Bool) 0 1 true { top => true",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn tubes_with_the_same_cap_must_agree_on_their_entire_overlap() {
    for optimized in [false, true] {
        let options = Options {
            optimized,
            ..Default::default()
        };
        let error = CheckedProgram::check_surface_with(
            r#"
            def bad (p : true == true) (q : true == true) : Bool =
              com (i => Bool) 0 1 true { top => p @ i; top => q @ i }
        "#,
            options,
        )
        .unwrap_err();
        assert!(
            error
                .message
                .contains("composition tubes disagree on an overlap")
        );
        CheckedProgram::check_surface_with(
            r#"
            def good (p : true == true) : Bool =
              com (i => Bool) 0 1 true { top => p @ i; top => p @ i }
            def disjoint (p : true == true) (q : true == true) : true == true =
              path j => com (i => Bool) 0 1 true { j = 0 => p @ i; j = 1 => q @ i }
        "#,
            options,
        )
        .unwrap();
    }
}

#[test]
fn conjunction_binds_more_tightly_than_disjunction_and_bottom_is_vacuous() {
    let error = CheckedProgram::check_surface(
        r#"
        def bad : Bool = com (i => Bool) 0 1 false { top || bottom && bottom => true }
    "#,
    )
    .unwrap_err();
    assert!(
        error
            .message
            .contains("composition tube disagrees with its cap at the source")
    );
    let program = CheckedProgram::check_surface(
        r#"
        def good : Bool = com (i => Bool) 0 1 false { (top || bottom) && bottom => true }
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("good").unwrap().text, "false");
}
