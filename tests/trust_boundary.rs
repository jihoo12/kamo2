use kamo::{CheckedProgram, MAX_SOURCE_BYTES};

#[test]
fn deeply_nested_surface_input_returns_errors_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let cases = [
                format!(
                    "def value : Bool = {}true{}",
                    "(".repeat(10_000),
                    ")".repeat(10_000)
                ),
                format!("def value : Bool = {}true", "let x = true; ".repeat(10_000)),
                format!("def value : Type = {}Bool", "Bool -> ".repeat(10_000)),
                format!("def value : Bool = {}true", "fst ".repeat(10_000)),
                format!("def value : Bool = f {}", "true ".repeat(10_000)),
                format!("def value : Bool = p {}", "@ 0 ".repeat(10_000)),
                format!(
                    "def value : Bool = system Bool {{ {} => true }}",
                    "top || ".repeat(10_000) + "top"
                ),
                format!(
                    "def value : Bool = system Bool {{ {}top{} => true }}",
                    "(".repeat(10_000),
                    ")".repeat(10_000)
                ),
            ];
            for source in cases {
                let error = CheckedProgram::check_surface(&source).unwrap_err();
                assert!(error.message.contains("budget exceeded"), "{error}");
                assert!(kamo::surface::parser::parse(&source).is_err());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn surface_parser_enforces_source_limit_for_direct_callers() {
    let source = " ".repeat(MAX_SOURCE_BYTES + 1);
    assert!(
        kamo::surface::parser::parse(&source)
            .unwrap_err()
            .message
            .contains("size budget")
    );
}

#[test]
fn oversized_surface_imports_are_rejected() {
    let root = std::env::temp_dir().join(format!("kamo-trust-files-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
        root.join("Main.kamo"),
        "import Large\ndef value : Bool = true",
    )
    .unwrap();
    let file = std::fs::File::create(root.join("Large.kamo")).unwrap();
    file.set_len((MAX_SOURCE_BYTES as u64) * 32).unwrap();
    let error = CheckedProgram::check_surface_file(root.join("Main.kamo")).unwrap_err();
    assert!(
        error.message.contains("source size budget exceeded"),
        "{error}"
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn parameter_lists_and_combined_ast_depth_are_bounded() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            for source in [
                format!("def value {}: Bool = true", "(x : Bool) ".repeat(5000)),
                format!("data Large {}: Type where {{}}", "(A : Type) ".repeat(5000)),
            ] {
                assert!(
                    CheckedProgram::check_surface(&source)
                        .unwrap_err()
                        .message
                        .contains("parameter budget")
                );
            }
            let mut expr = "true".to_string();
            for _ in 0..3 {
                expr = format!("({expr}) {}", "true ".repeat(64));
            }
            let source = format!("def value : Bool = {expr}");
            assert!(
                kamo::surface::parser::parse(&source)
                    .unwrap_err()
                    .message
                    .contains("AST depth budget")
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
