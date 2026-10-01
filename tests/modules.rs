use kamo::CheckedProgram;
use std::fs;

#[test]
fn surface_data_and_transitive_modules_work_together() {
    let root = std::env::temp_dir().join(format!("kamo-modules-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("Option.kamo"),
        r#"
            module Option
            data Option (A : Type) : Type where {
              none : Option A;
              some : A -> Option A
            }
            def present : Option Bool = some Bool true
        "#,
    )
    .unwrap();
    fs::write(
        root.join("Main.kamo"),
        r#"
            module Main
            import Option
            def get-or-false (x : Option Bool) : Bool =
              match x { none => false; some value => value }
            def answer : Bool = get-or-false (some Bool true)
        "#,
    )
    .unwrap();

    let program = CheckedProgram::check_surface_file(root.join("Main.kamo")).unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "true");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn standard_nat_and_bool_are_generic_data() {
    let program = CheckedProgram::check_surface(
        r#"
            def flip (b : Bool) : Bool = match b { true => false; false => true }
            def answer : Bool = flip false
            def one : Nat = suc zero
            def singleton (A : Type) (x : A) : Vec A (suc zero) =
              cons A zero x (nil A)
            def one-bool : Vec Bool (suc zero) = singleton Bool true
        "#,
    )
    .unwrap();
    assert_eq!(program.normalize("answer").unwrap().text, "true");
    assert_eq!(program.normalize("one").unwrap().text, "(app suc zero)");
    assert_eq!(
        program.normalize("one-bool").unwrap().text,
        "(app (app (app (app cons Bool) zero) true) (app nil Bool))"
    );
}

#[test]
fn strict_positivity_rejects_negative_nested_and_non_uniform_recursion() {
    for (source, expected) in [
        (
            "data Bad : Type where { bad : (Bad -> Nat) -> Bad }",
            "nested or negative recursive occurrence",
        ),
        (
            "data Bad : Type where { bad : Vec Bad zero -> Bad }",
            "nested or negative recursive occurrence",
        ),
        (
            "data Bad (A : Type) : Type where { bad : Bad Bool -> Bad A }",
            "changes a uniform parameter",
        ),
    ] {
        let error = CheckedProgram::check_surface(source).unwrap_err();
        assert!(error.message.contains(expected), "{error}");
    }
}

#[test]
fn inductive_telescopes_are_semantically_checked() {
    let error =
        CheckedProgram::check_surface("data Bad : Type where { bad : (not-a-type : true) -> Bad }")
            .unwrap_err();
    assert!(error.message.contains("expected a type"), "{error}");
}


#[test]
fn constructor_fields_respect_the_declared_inductive_universe() {
    let error =
        CheckedProgram::check_surface("data TooLarge : Type where { large : Type -> TooLarge }")
            .unwrap_err();
    assert!(
        error.message.contains("above inductive universe"),
        "{error}"
    );

    CheckedProgram::check_surface("data Large : Type1 where { large : Type -> Large }").unwrap();
}

#[test]
fn surface_declaration_names_share_one_namespace() {
    for source in [
        "data Clash : Type where { Clash : Clash }",
        "def taken : Bool = true data D : Type where { taken : D }",
        "data D : Type where { ctor : D } def ctor : D = ctor",
    ] {
        let error = CheckedProgram::check_surface(source).unwrap_err();
        assert!(
            error.message.contains("duplicate") || error.message.contains("reserved"),
            "{source}: {error}"
        );
    }
}

#[test]
fn anonymous_constructor_arrows_do_not_create_source_names() {
    let error = CheckedProgram::check_surface(
        "data Hidden : Type1 where { hidden : Type -> _arg0 -> Hidden }",
    )
    .unwrap_err();
    assert!(error.message.contains("unknown name '_arg0'"), "{error}");
}

#[test]
fn transitive_import_depth_is_bounded() {
    let root = std::env::temp_dir().join(format!(
        "kamo-deep-modules-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();

    for index in 0..=64 {
        let source = if index < 64 {
            format!("module M{index}\nimport M{}\n", index + 1)
        } else {
            format!("module M{index}\n")
        };
        fs::write(root.join(format!("M{index}.kamo")), source).unwrap();
    }

    let error = CheckedProgram::check_surface_file(root.join("M0.kamo")).unwrap_err();
    assert!(
        error.message.contains("module import depth budget exceeded"),
        "{error}"
    );
    fs::remove_dir_all(root).unwrap();
}
