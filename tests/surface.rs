use kamo::CheckedProgram;

fn surface_nf(source: &str, name: &str) -> String {
    CheckedProgram::check_surface(source)
        .unwrap()
        .normalize(name)
        .unwrap()
        .text
}

#[test]
fn documentation_style_id_and_twice() {
    let source = r#"
        def id (A : Type) (x : A) : A = x

        def twice (A : Type) (f : A -> A) (x : A) : A =
          f (f x)

        def result : Bool = twice Bool (\x => x) true
    "#;
    let program = CheckedProgram::check_surface(source).unwrap();
    assert_eq!(
        program.names().collect::<Vec<_>>(),
        ["id", "twice", "result"]
    );
    assert_eq!(program.normalize("result").unwrap().text, "true");
}

#[test]
fn dependent_pi_and_let_elaborate_directly() {
    let source = r#"
        def dep : (A : Type) -> A -> A = \A => \x => x
        def id (A : Type) (x : A) : A = x
        def via-let : Bool = let x = true; x
        def via-app-let : Bool = let f = id Bool; f true
        def local-let (A : Type) (x : A) : A = let y = x; y
    "#;
    assert_eq!(surface_nf(source, "via-let"), "true");
    assert_eq!(surface_nf(source, "via-app-let"), "true");
}

#[test]
fn universes_are_explicit_and_cumulative() {
    CheckedProgram::check_surface(
        r#"
            def small : Type1 = Bool
            def universe : Type2 = Type
        "#,
    )
    .unwrap();
}

#[test]
fn surface_type_errors_reach_the_kernel() {
    let error = CheckedProgram::check_surface("def bad : Bool = zero").unwrap_err();
    assert!(error.message.contains("type mismatch"), "{error}");
}

#[test]
fn existing_core_entry_point_is_unchanged() {
    let program = CheckedProgram::check("(def x Bool true)").unwrap();
    assert_eq!(program.normalize("x").unwrap().text, "true");
}

const TAG: &str = r#"
    data Tag : Nat -> Type where {
      tzero : Tag zero;
      tsuc : (n : Nat) -> Tag (suc n)
    }
"#;

#[test]
fn dependent_tag_match_refines_constructor_indices() {
    let source = format!(
        r#"{TAG}
        def idTag (n : Nat) (x : Tag n) : Tag n =
          match x {{ tzero => tzero; tsuc m => tsuc m }}
        def z : Tag zero = idTag zero tzero
        def s : Tag (suc zero) = idTag (suc zero) (tsuc zero)
    "#
    );
    let program = CheckedProgram::check_surface(&source).unwrap();
    assert_eq!(program.normalize("z").unwrap().text, "tzero");
    assert_eq!(program.normalize("s").unwrap().text, "(app tsuc zero)");
}

#[test]
fn dependent_vec_motive_preserves_parameters_and_scrutinee() {
    let source = r#"
        data Witness (A : Type) : (n : Nat) -> Vec A n -> Type where {
          witness : (m : Nat) -> (ys : Vec A m) -> Witness A m ys
        }
        def witnessVec (A : Type) (n : Nat) (xs : Vec A n) : Witness A n xs =
          match xs {
            nil => witness A zero (nil A);
            cons m head tail => witness A (suc m) (cons A m head tail)
          }
        def result : Witness Bool zero (nil Bool) = witnessVec Bool zero (nil Bool)
    "#;
    assert_eq!(
        surface_nf(source, "result"),
        "(app (app (app witness Bool) zero) (app nil Bool))"
    );
}

#[test]
fn dependent_vec_copy_uses_tail_index_for_recursive_ih() {
    let source = r#"
        def copy (A : Type) (n : Nat) (xs : Vec A n) : Vec A n =
          match xs {
            nil => nil A;
            cons m head tail => let copied = copy A m tail; cons A m head copied
          }
        def input : Vec Bool (suc (suc zero)) =
          cons Bool (suc zero) true (cons Bool zero false (nil Bool))
        def output : Vec Bool (suc (suc zero)) = copy Bool (suc (suc zero)) input
    "#;
    let program = CheckedProgram::check_surface(source).unwrap();
    assert_eq!(
        program.normalize("input").unwrap().text,
        program.normalize("output").unwrap().text
    );
}

#[test]
fn dependent_match_rejects_wrong_refined_index() {
    for branches in [
        "tzero => tsuc zero; tsuc m => tsuc m",
        "tzero => tzero; tsuc m => tzero",
    ] {
        let source =
            format!("{TAG} def bad (n : Nat) (x : Tag n) : Tag n = match x {{ {branches} }}");
        let error = CheckedProgram::check_surface(&source).unwrap_err();
        assert!(error.message.contains("type mismatch"), "{error}");
    }
}

#[test]
fn dependent_match_handles_shadowing_and_result_binders() {
    let source = r#"
        def rebuild (A : Type) (n : Nat) (xs : Vec A n) : Vec A n =
          match xs { nil => nil A; cons n xs tail => cons A n xs tail }
        def functions (A : Type) (n : Nat) (xs : Vec A n) : (n : A) -> Vec A n =
          match xs { nil => \x => nil A; cons m head tail => \x => cons A m head tail }
    "#;
    // The binder in the second result deliberately shadows the index: its type
    // is invalid, and refinement must not accidentally make it valid.
    let error = CheckedProgram::check_surface(source).unwrap_err();
    assert!(error.message.contains("type mismatch"), "{error}");
    CheckedProgram::check_surface(&source.replace("(n : A) -> Vec A n", "(x : A) -> Vec A n"))
        .unwrap();
}

#[test]
fn dependent_match_instantiates_compound_parameters() {
    CheckedProgram::check_surface(r#"
        def rebuild (n : Nat) (xs : Vec (Vec Bool zero) n) : Vec (Vec Bool zero) n =
          match xs { nil => nil (Vec Bool zero); cons m head tail => cons (Vec Bool zero) m head tail }
    "#).unwrap();
}

#[test]
fn match_still_requires_expected_type_and_valid_patterns() {
    for (source, message) in [
        (
            "def f (b : Bool) : Bool = let x = match b { true => true; false => false }; x",
            "cannot infer surface match",
        ),
        (
            "def f (b : Bool) : Bool = match b { true => true }",
            "non-exhaustive",
        ),
        (
            "def f (b : Bool) : Bool = match b { true => true; true => false; false => false }",
            "duplicate match branch",
        ),
        (
            "def f (b : Bool) : Bool = match b { true x => true; false => false }",
            "pattern arguments",
        ),
        (
            "def f (b : Bool) : Bool = match b { true => true; zero => false }",
            "same inductive family",
        ),
    ] {
        let error = CheckedProgram::check_surface(source).unwrap_err();
        assert!(error.message.contains(message), "{error}");
    }
}

#[test]
fn refined_branch_type_reaches_lambda_and_let_contexts() {
    let source = format!(
        r#"{TAG}
        def f (n : Nat) (x : Tag n) : Tag n -> Tag n =
          match x {{
            tzero => \y => let z = y; z;
            tsuc m => \y => let z = y; z
          }}
        def result : Tag zero = f zero tzero tzero
    "#
    );
    assert_eq!(surface_nf(&source, "result"), "tzero");
}

#[test]
fn motive_preserves_dependent_index_telescope() {
    CheckedProgram::check_surface(
        r#"
        data Packed (A : Type) : (n : Nat) -> Vec A n -> Type where {
          pack : (m : Nat) -> (ys : Vec A m) -> Packed A m ys
        }
        def rebuild (A : Type) (n : Nat) (xs : Vec A n) (p : Packed A n xs) : Packed A n xs =
          match p { pack m ys => pack A m ys }
    "#,
    )
    .unwrap();
}

#[test]
fn nondependent_motive_keeps_outer_parameter_under_new_binders() {
    CheckedProgram::check_surface(
        r#"
        def choose (A : Type) (a : A) (n : Nat) (xs : Vec A n) : A =
          match xs { nil => a; cons m head tail => head }
    "#,
    )
    .unwrap();
}

#[test]
fn nondependent_match_preserves_let_in_expected_type() {
    CheckedProgram::check_surface(
        r#"
        def f (b : Bool) : (let A = Bool; A) = match b { true => false; false => true }
    "#,
    )
    .unwrap();
}
