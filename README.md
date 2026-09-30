# Kamo2

Kamo2 is an experimental **cubical dependently typed functional language** in
Rust.

It grows out of [Kamo](https://github.com/jihoo12/kamo), whose small Cartesian
cubical kernel is the starting point. Kamo2 keeps that cubical foundation while
developing a functional surface language, user-defined inductive families, and
eventually higher inductive types.

> Kamo2 is experimental. The current implementation is still close to the Kamo
> kernel; most of the functional surface language and general inductive/HIT
> design described below is roadmap work, not implemented language syntax yet.

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

## Planned surface language

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

These examples describe the target surface language. They are not all accepted
by the current parser.

## Current implementation

The current executable still exposes Kamo's explicit S-expression core
language. It includes:

- dependent functions (`Pi`) and pairs (`Sigma`);
- explicit universes;
- primitive `Bool` and `Nat` with dependent eliminators;
- dependent paths and interval application;
- coercion and heterogeneous composition;
- systems and `Glue`;
- normalization-by-evaluation style semantic checking/evaluation machinery;
- resource limits and reference/optimized evaluator modes.

There are currently no unrestricted recursive definitions, general
user-defined inductive families, higher inductive types, or completed
ML-style pattern matching.

The repository already contains an initial `surface` module, but the existing
S-expression parser remains the usable frontend while the new language is
developed.

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

Primitive `Nat` and `Bool` will remain during this transition so the generic
implementation can be tested against the existing behavior.

Pattern matching is intended to elaborate to dependent eliminators rather than
becoming a separate evaluator mechanism.

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

The current working order is:

```text
cumulative universe checking
        |
        v
minimal functional syntax
        |
        v
checked inductive metadata
        |
        v
ordinary inductive types
        |
        v
indexed families: Vec / Fin
        |
        v
dependent eliminators
        |
        v
pattern matching + structural recursion
        |
        v
cubical surface syntax
        |
        v
higher inductive types: Circle
```

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
