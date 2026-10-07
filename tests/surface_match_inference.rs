use kamo::{CheckedProgram, Options};

#[test]
fn explicit_matches_infer_let_and_function_types_in_both_modes() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/inferred-match-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(program.normalize("result").unwrap().text, "true");
        assert_eq!(
            program.normalize("copied").unwrap().text,
            program.normalize("singleton").unwrap().text
        );
    }
}

#[test]
fn inferred_motives_substitute_typed_expression_scrutinees() {
    CheckedProgram::check_surface(
        r#"
        def proof (n : Nat) : (suc n) == (suc n) =
          let p = match (suc n) return (value => value == value) {
            zero => path i => zero;
            suc k => path i => suc k
          }; p
        def endpoint : Nat =
          (match (suc zero) return (value => value == value) {
            zero => path i => zero;
            suc k => path i => suc k
          }) @ 1
    "#,
    )
    .unwrap();
}

#[test]
fn reification_prevents_capture_by_function_and_pair_binders() {
    CheckedProgram::check_surface(
        r#"
        def make (x : Nat) : (y : Nat) -> x == x =
          let f = match x return (value => (x : Nat) -> value == value) {
            zero => \x => path i => zero;
            suc k => \x => path i => suc k
          }; f
        def pack (x : Nat) : Sigma (y : Nat) => y == x =
          let p = match x return (value => Sigma (x : Nat) => x == value) {
            zero => (zero, path i => zero);
            suc k => (suc k, path i => suc k)
          }; p
    "#,
    )
    .unwrap();
}

#[test]
fn dependent_index_metadata_and_repeated_indices_are_instantiated() {
    CheckedProgram::check_surface(
        r#"
        data Indexed : (A : Type) -> A -> Type1 where {
          mk : (A : Type) -> (x : A) -> Indexed A x
        }
        def rebuild (A : Type) (x : A) (p : Indexed A x) : Indexed A x =
          let q = match p return (B, y, value => Indexed B y) { mk B y => mk B y }; q
        data Tagged : Nat -> Nat -> Type where { tag : (a : Nat) -> (b : Nat) -> Tagged a b }
        def repeated (n : Nat) (p : Tagged n n) : Tagged n n =
          let q = match p return (a, b, value => Tagged a b) { tag a b => tag a b }; q
    "#,
    )
    .unwrap();
}

#[test]
fn inferred_matches_retain_nested_pattern_and_structural_recursion_support() {
    CheckedProgram::check_surface(
        r#"
        def subtract (n : Nat) : Nat =
          let result = match n return (value => Nat) {
            zero => zero; suc (zero) => zero; suc (suc k) => k
          }; result
        def copy (n : Nat) : Nat =
          let result = match n return (value => Nat) {
            zero => zero; suc k => suc (copy k)
          }; result
    "#,
    )
    .unwrap();
}

#[test]
fn inferred_match_paths_preserve_the_outer_dimension_scope() {
    CheckedProgram::check_surface(
        r#"
        def id (A : Type) (x : A) : A = x
        def ids (A : Type) (p : A == A) : PathP (j => p @ j -> p @ j) (id A) (id A) =
          path j => let result = match true return (value => p @ j -> p @ j) {
            true => \x => x; false => \x => x
          }; result
    "#,
    )
    .unwrap();
}

#[test]
fn inference_does_not_bypass_branch_coverage_or_kernel_type_checks() {
    for source in [
        "def bad (n : Nat) : Nat = let x = match n return (value => Nat) { zero => true; suc k => k }; x",
        "def bad (n : Nat) : Nat = let x = match n return (value => Bool) { zero => true; suc k => false }; x",
        "def bad (n : Nat) : Nat = let x = match n return (value => value) { zero => zero; suc k => k }; x",
        "def bad (n : Nat) : Nat = let x = match n return (value => Nat) { zero => zero }; x",
        "def bad (n : Nat) : Nat = let x = match n return (a, b => Nat) { zero => zero; suc k => k }; x",
        "def bad (n : Nat) : Nat = let x = match n { zero => zero; suc k => k }; x",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn inferred_matches_support_compound_indices_and_dependent_projections() {
    CheckedProgram::check_surface(
        r#"
        def copySuccessor (A : Type) (n : Nat) (xs : Vec A (suc n)) : Vec A (suc n) =
          let copied = match xs return (length, value => Vec A length) {
            nil => nil A; cons k head tail => cons A k head tail
          }; copied
        def pack (n : Nat) : Sigma (value : Nat) => value == n =
          let packed = match n return (value => Sigma (m : Nat) => m == value) {
            zero => (zero, path i => zero); suc k => (suc k, path i => suc k)
          }; (fst packed, snd packed)
    "#,
    )
    .unwrap();
}
