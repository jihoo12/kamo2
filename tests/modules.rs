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
