use kamo::{CheckedProgram, Options};

#[test]
fn explicit_vector_motives_check_compound_indices_and_structural_recursion() {
    for optimized in [false, true] {
        let program = CheckedProgram::check_surface_with(
            include_str!("../examples/match-motives-surface.kamo"),
            Options {
                optimized,
                ..Default::default()
            },
        )
        .unwrap();
        assert_eq!(
            program.normalize("result").unwrap().text,
            program.normalize("singleton").unwrap().text
        );
    }
}

#[test]
fn explicit_motives_abstract_expression_scrutinees() {
    CheckedProgram::check_surface(
        r#"
        def refl (n : Nat) : (suc n) == (suc n) =
          match (suc n) return (value => value == value) {
            zero => path i => zero;
            suc k => path i => suc k
          }
    "#,
    )
    .unwrap();
}

#[test]
fn repeated_indices_can_be_generalized_independently_by_an_explicit_motive() {
    CheckedProgram::check_surface(
        r#"
        data Tagged : Nat -> Nat -> Type where {
          tag : (a : Nat) -> (b : Nat) -> Tagged a b
        }
        def preserve (n : Nat) (x : Tagged n n) : Tagged n n =
          match x return (a, b, value => Tagged a b) {
            tag i j => tag i j
          }
    "#,
    )
    .unwrap();
}

#[test]
fn explicit_motive_binders_do_not_capture_branch_or_outer_variables() {
    CheckedProgram::check_surface(
        r#"
        def preserve (A : Type) (n : Nat) (xs : Vec A n) : Vec A n =
          match xs return (n, xs => Vec A n) {
            nil => nil A;
            cons n x xs => cons A n x xs
          }
        def witness (n : Nat) : n == n =
          match n return (n => n == n) {
            zero => path n => zero;
            suc n => path n => suc n
          }
    "#,
    )
    .unwrap();
}

#[test]
fn explicit_motives_support_dependent_pair_and_path_results() {
    CheckedProgram::check_surface(
        r#"
        def pack (n : Nat) : Sigma (k : Nat) => k == n =
          match n return (value => Sigma (k : Nat) => k == value) {
            zero => (zero, path i => zero);
            suc k => (suc k, path i => suc k)
          }
    "#,
    )
    .unwrap();
}

#[test]
fn motives_and_branches_are_independently_checked_by_the_kernel() {
    for source in [
        "def bad (n : Nat) : Bool = match n return (value => Nat) { zero => zero; suc k => suc k }",
        "def bad (n : Nat) : Nat = match n return (value => Nat) { zero => true; suc k => suc k }",
        "def bad (n : Nat) : Nat = match n return (value => value) { zero => zero; suc k => suc k }",
        "def bad (n : Nat) : Nat = match n return (value => Nat) { zero => zero }",
        "def bad (n : Nat) : Nat = match n return (value => Nat) { zero => zero; zero => zero; suc k => suc k }",
        "def bad (n : Nat) : Nat = match n return (value => Nat) { zero => value; suc k => suc k }",
        "def bad (n : Nat) : Nat = match n return (value => Nat) { zero => zero; suc k => bad (suc k) }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn motive_binder_arity_and_uniqueness_are_validated() {
    for source in [
        "def bad (n : Nat) : Nat = match n return (a, b => Nat) { zero => zero; suc k => suc k }",
        "def bad (A : Type) (n : Nat) (xs : Vec A n) : Vec A n = match xs return (a, a => Vec A a) { nil => nil A; cons k x xs => cons A k x xs }",
        "def bad (n : Nat) : Nat = match n return (=> Nat) { zero => zero; suc k => suc k }",
    ] {
        assert!(CheckedProgram::check_surface(source).is_err(), "{source}");
    }
}

#[test]
fn constructor_applications_infer_their_full_dependent_result_type() {
    let program = CheckedProgram::check_surface(
        r#"
        def vector : Vec Bool (suc zero) =
          let xs = cons Bool zero true (nil Bool);
          match xs return (n, value => Vec Bool n) {
            nil => nil Bool;
            cons k x tail => cons Bool k x tail
          }
        def empty : Vec Bool zero = let xs = nil Bool; xs
        def number : Nat = let n = suc zero; n
    "#,
    )
    .unwrap();
    assert_eq!(program.normalize("number").unwrap().text, "(app suc zero)");
    assert!(
        CheckedProgram::check_surface(
            r#"
        def bad : Vec Bool zero = let xs = cons Bool zero true (nil Bool); xs
    "#
        )
        .is_err()
    );
}

#[test]
fn explicit_motive_indices_keep_their_dependent_metadata_types() {
    CheckedProgram::check_surface(
        r#"
        data Indexed : (A : Type) -> A -> Type1 where {
          mk : (A : Type) -> (x : A) -> Indexed A x
        }
        def rebuild (A : Type) (x : A) (p : Indexed A x) : Indexed A x =
          match p return (B, y, value => Indexed B y) { mk B y => mk B y }
    "#,
    )
    .unwrap();
}
