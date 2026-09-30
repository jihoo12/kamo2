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
