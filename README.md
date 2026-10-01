# Kamo2

Kamo2 is an experimental **cubical dependently typed functional language** in
Rust.

It grows out of [Kamo](https://github.com/jihoo12/kamo), whose small Cartesian
cubical kernel is the starting point. Kamo2 keeps that cubical foundation while
developing a functional surface language, user-defined inductive families, and
eventually higher inductive types.

> Kamo2 is experimental. The command-line tool still uses the explicit
> S-expression core language by default. A functional surface parser and elaborator
> are available through the library API, including typed definitions, functions,
> `let` expressions, exhaustive constructor matching, and structural recursion.
> Surface `data` declarations, file modules, and ordinary pattern matching are
> available; dependent matching, cubical surface syntax, and higher inductive
> types remain roadmap work.

## Direction

The intended architecture is:

```text
functional surface language
        |
        v
name resolution / elaboration
        |
        v
inductive-family + cubical elaboration
        |
        v
small cubical dependent core
        |
        v
checker / evaluator
```

Ordinary functional code should look ordinary. Cubical structure should become
visible when a program actually works with equality, transport, composition, or
higher-dimensional data.

The two main architecture milestones are:

- **Vec:** general indexed inductive families, dependent elimination, and later
  dependent pattern matching.
- **Circle:** higher inductive types with path constructors and cubical
  elimination/coherence.

In short: make `Vec` principled first, then make `Circle` principled.

See [language direction](docs/language-design.md),
[inductive-family design](docs/inductive-types.md), and
[universe design](docs/universes.md).

## Surface language direction

The surface language is intended to grow toward code like:

```text
def id (A : Type) (x : A) : A =
  x

def twice (A : Type) (f : A -> A) (x : A) : A =
  f (f x)

data Vec (A : Type) : Nat -> Type where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)
```

Cubical equality is intended to be path equality rather than a second,
unrelated equality type:

```text
def refl (x : A) : x == x =
  path i => x

def cong (f : A -> B) (p : x == y) : f x == f y =
  path i => f (p @ i)
```

The parser accepts typed `def` declarations, parameters, function types,
lambdas, application, `let`, `data`, `module`, and `import`. `Bool`, `Nat`, and
`Vec` are now ordinary declarations in `std/prelude.kamo`, not special surface
syntax. Cubical path syntax remains future work.

## Current implementation

The command-line executable still exposes Kamo's explicit S-expression core
language. The core includes:

- dependent functions (`Pi`) and pairs (`Sigma`);
- explicit universes;
- primitive `Bool` and `Nat` with dependent eliminators;
- dependent paths and interval application;
- coercion and heterogeneous composition;
- systems and `Glue`;
- checked metadata and semantics for indexed inductive families and
  constructors;
- dependent inductive eliminators with iota computation;
- trusted strict-positivity/metadata validation and conservative structural
  composition for generic ordinary inductives;
- normalization-by-evaluation style semantic checking/evaluation machinery;
- resource limits and reference/optimized evaluator modes.

The library API also exposes `CheckedProgram::check_surface` and
`check_surface_with`. The surface parser/elaborator currently supports:

- typed definitions and parameters;
- dependent and non-dependent function types, lambdas, and application;
- `let` expressions;
- surface declarations for parameterized and indexed inductive families;
- exhaustive constructor patterns for a single inductive family;
- non-dependent matches lowered to the core dependent eliminator;
- structural recursive calls lowered to the corresponding eliminator
  hypotheses.

Constructor arity, duplicate branches, family consistency, and exhaustiveness
are checked during elaboration. Structural recursion is restricted to calls
recognized through recursive constructor arguments; unrestricted recursion is
not accepted.

The `check-surface` and `normalize-surface` CLI modes load transitive file
imports. An import such as `import Data.Vec` resolves `Data/Vec.kamo` relative
to the importing module. Dependent pattern matching, cubical surface syntax,
and higher inductive types are not implemented.

## Universes

The inherited implementation currently has explicit **non-cumulative**
universes. Kamo2's design direction is explicit **cumulative** universes:

```text
U i : U (i + 1)

A : U i    i <= j
-----------------
A : U j
```

Different universes will not become definitionally equal. Cumulativity is
planned as a separate checking/compatibility relation, without a runtime
`Lift` term.

For dependent function and pair formation, the intended principal level is:

```text
level(Pi A B)    = max(level(A), level(B))
level(Sigma A B) = max(level(A), level(B))
```

Universe polymorphism and level inference are later work. See
[docs/universes.md](docs/universes.md).

## Inductive families

General inductive families are planned as checked core metadata rather than
being hidden entirely behind an encoding.

The current design separates:

1. checked inductive/constructor metadata;
2. generic family and constructor values;
3. dependent eliminators and iota computation;
4. surface `data` elaboration;
5. cubical composition for the supported inductive fragment.

The core primitives remain for compatibility with the S-expression language,
but surface `Nat`, `Bool`, and `Vec` use the same generic inductive-family
metadata, eliminator, and iota computation as user declarations.
Generic composition is constructor-directed and covers direct-recursive,
parameterized, and indexed examples when parameters, dependent field types, and
result indices are definitionally coherent. Ambiguous or varying cases remain
neutral rather than applying an unsound fallback.

Non-dependent surface pattern matching now elaborates to the existing
dependent eliminators rather than adding a separate evaluator mechanism.
Structural recursive calls are lowered to eliminator hypotheses. Surface
dependent pattern matching remains future work.

## Higher inductive types

HITs come after ordinary inductive families have a clear trusted
representation, elimination rule, and cubical composition behavior.

The canonical target is:

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

A path constructor such as `loop` cannot be treated as an ordinary point
constructor. Its elimination rule needs boundary/coherence information and
should reuse Kamo's existing path/composition machinery.

## Current core syntax

Definitions currently use:

```text
(def name type body)
```

Later definitions may refer to earlier definitions. `;` begins a line
comment.

| Form | Meaning |
| --- | --- |
| `(U level)` | Universe; currently non-cumulative in the implementation |
| `(Pi x A B)`, `(lam x body)`, `(app f x)` | Dependent function, introduction, application |
| `(Sigma x A B)`, `(pair a b)`, `(fst p)`, `(snd p)` | Dependent pair and projections |
| `Bool`, `true`, `false` | Primitive Booleans |
| `(bool-elim motive true-case false-case value)` | Dependent Boolean elimination |
| `Nat`, `zero`, `(suc n)` | Primitive natural numbers |
| `(nat-elim motive zero-case step value)` | Dependent natural elimination |
| `(Path i A left right)`, `(path i body)`, `(at p r)` | Dependent paths and interval application |
| `(coe i A r s cap)` | Transport in a type family |
| `(com i A r s cap ((face tube) ...))` | Heterogeneous composition |
| `(system A ((face value) ...))` | Compatible system |
| `(Glue B ((face A equivalence) ...))` | Glue type |
| `(glue G base ((face value) ...))` | Glue introduction |
| `(unglue G value)` | Glue projection |

Dimensions are `0`, `1`, or bound interval names. Faces are `top`,
`bottom`, `(= r s)`, `(and phi psi)`, or `(or phi psi)`.

See [rule correspondence](docs/rules.md) for the current core theory and
implementation boundary.

## Build and run

```sh
cargo build --release
scripts/with-limits.sh target/release/kamo check examples/univalence.kamo
scripts/with-limits.sh target/release/kamo normalize examples/univalence.kamo neg-true
# false
```

The Cargo package and executable are still named `kamo` during the early
transition.

A smaller dependent example is natural-number addition:

```sh
scripts/with-limits.sh target/release/kamo check examples/nat-add.kamo
scripts/with-limits.sh target/release/kamo normalize examples/nat-add.kamo four
# (suc (suc (suc (suc zero))))
```

The existing examples also exercise univalence, foundational path lemmas,
categories, functors, and natural transformations.

## Tests

CI checks formatting, Clippy, and the Rust test suite.

Locally:

```sh
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all-targets --all-features --locked
```

For constrained kernel runs, the repository also provides
`scripts/with-limits.sh`.

## Resource limits

The checker/evaluator uses explicit fuel and arena-node budgets. The development
runner additionally applies process limits.

A resource-limit failure is an inconclusive check, not a successful proof and
not a proof that a proposition is false.

Use `--stats` with normalization to inspect evaluator work and arena usage.
The `--reference` mode disables several optimizations so tests can compare the
optimized and reference implementations under the same mathematical reduction
rules.

## Development roadmap

Completed foundations:

- [x] minimal functional surface syntax;
- [x] direct surface-to-core elaboration;
- [x] checked inductive and constructor metadata;
- [x] indexed inductive-family and constructor semantics;
- [x] dependent inductive eliminators;
- [x] conservative generic ordinary-inductive composition;
- [x] surface `data` declarations for ordinary and indexed families;
- [x] non-dependent pattern matching and structural recursion lowering.

Next milestones:

- [ ] dependent pattern matching;
- [ ] cubical surface syntax;
- [ ] higher inductive types, beginning with `Circle`.

Near-term work intentionally avoids unrestricted general recursion, a separate
propositional equality type, broad global type inference, and premature HIT
syntax.

## Status and trust

Kamo2 is a research/experimental implementation. It is not formally verified,
and the metatheory of the planned general inductive and higher-inductive
extensions has not been independently audited.

The inherited Kamo core includes checked examples of equivalences, `ua`, and
univalence. New Kamo2 features should preserve the project's small,
auditable trusted boundary rather than moving surface conveniences directly
into the kernel.

Kamo2 is licensed under the repository's Apache-2.0 license. The project is
derived from [Kamo](https://github.com/jihoo12/kamo).
