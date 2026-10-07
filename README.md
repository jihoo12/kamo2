# Kamo2

Kamo2 is an experimental **cubical dependently typed functional language** in
Rust.

It grows out of [Kamo](https://github.com/jihoo12/kamo), whose small Cartesian
cubical kernel is the starting point. Kamo2 keeps that cubical foundation while
developing a functional surface language, user-defined inductive families, and a
scoped first higher-inductive milestone around Circle.

This README and [docs/rules.md](docs/rules.md) describe the implemented core and
its trust boundary. Other design documents are explicitly labeled as proposals
or future roadmaps where they go beyond the current implementation.

> Kamo2 is experimental. The command-line tool still uses the explicit
> S-expression core language by default. A functional surface parser and elaborator
> are available through the library API, including typed definitions, functions,
> `let` expressions, exhaustive constructor matching, and structural recursion.
> Surface `data` declarations, file modules, and ordinary pattern matching are
> available, including expected-type-directed dependent constructor refinement
> for ordinary indexed families. Homogeneous path equality (`==`), path
> abstractions, path application, and the scoped `data Circle` declaration are
> available. Transport (`coe`) and composition (`com`) have surface syntax. General higher
> inductive types remain roadmap work.

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

- **Vec:** general indexed inductive families, dependent elimination, and
  expected-type-directed dependent constructor refinement.
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

Surface equality is homogeneous cubical path equality, using the existing
checked core paths:

```text
def refl (A : Type) (x : A) : x == x =
  path i => x

def cong (A : Type) (B : Type) (f : A -> B)
  (x : A) (y : A) (p : x == y) : f x == f y =
  path i => f (p @ i)
```

The parser accepts typed `def` declarations, parameters, function types,
lambdas, application, `let`, `data`, `module`, and `import`. `Bool`, `Nat`, and
`Vec` are now ordinary declarations in `std/prelude.kamo`, not special surface
syntax. Path notation additionally supports `x == y`, `path i => t`, and
`p @ i` (also `p @ 0` and `p @ 1`). Equality infers its family from the left
endpoint and the kernel checks both endpoints against that constant family.
Path abstractions use expected types; general path-abstraction inference is
not available yet. Explicit dependent paths use `PathP (i => A) left right`,
where only the type family `A` binds `i`. The endpoints have types `A[0/i]`
and `A[1/i]`, respectively. A term `p @ r` of this path type has type `A[r/i]`.
The abstraction `path j => body` checks its body at `A[j/i]`, including
expected-type-directed lambdas and matches. Constant families convert to the
ordinary homogeneous equality `==`.

```text
def transportPath (A : Type) (B : Type) (p : A == B) (x : A) :
  PathP (i => p @ i) x (coe (i => p @ i) 0 1 x) =
  path j => coe (i => p @ i) 0 j x
```

`PathP` is atomic; parenthesize compound endpoints such as function applications,
lambdas, and matches. Each endpoint includes postfix `@`, and the family binder
does not scope over either endpoint. These paths lower to the existing core
`Path`; no new kernel rules are introduced. Inductive constructor metadata
retains its existing restrictions: families containing dimension application
(such as `p @ i`) are not supported inside constructor argument types yet.

Precedence, from tightest to loosest, is postfix `@`, ordinary application,
non-associative `==`, then right-associative `->`. Thus `f x == g y` compares
applications, `f p @ i` means `f (p @ i)`, and `(f x) @ i` applies a dimension to
the result of `f x`. Parenthesize chained equalities and abstractions used as
arguments. Dimension names use letters/digits/underscores, starting with a letter
or underscore; dimensions are separate from term variables and shadow lexically.
Only `0`, `1`, and bound dimension names are accepted as dimensions.

Transport uses `coe (i => A) r s value`, where `i` binds a dimension in the
type family `A` only. The endpoints `r` and `s` are `0`, `1`, or surrounding
bound dimensions. The value is checked at `A[r/i]`, and the result has type
`A[s/i]`. Parenthesize compound values, including lambdas and matches:

```text
def transport (A : Type) (B : Type) (p : A == B) (x : A) : B =
  coe (i => p @ i) 0 1 x
```

`coe` is an atomic expression; its value argument includes postfix `@` but
not unparenthesized function application. For example, use
`coe (i => A) 0 1 (f x)`. Parenthesize the whole transport before applying
`@` to its result. The family binder does not scope over endpoints or the
value. Transport elaborates to existing core composition with no tubes,
preserving the kernel's computation rules: equal endpoints compute to the
value, while unknown or varying families may remain neutral.

Composition uses `com (i => A) r s cap { face => tube; ... }`. The dimension
`i` binds the family and tube bodies, but not the endpoints, cap, or faces.
The cap is checked at `A[r/i]`, tubes at `A`, and the result has type `A[s/i]`.
The kernel checks that each tube agrees with the cap at `r` under its face,
and that tube bodies agree wherever their faces overlap. Faces need not cover
the whole context; empty tubes give the same operation as `coe`.

Faces are `top`, `bottom`, or dimension equalities such as `i = 0` and `i = j`,
combined with `&&`, `||`, and parentheses. Equality binds tighter than `&&`,
which binds tighter than `||`. These operators combine cofibrations; they
are not operations on interval values. There is no surface or core interval
meet, join, or reversal.

```text
def concat (A : Type) (x : A) (y : A) (z : A)
  (p : x == y) (q : y == z) : x == z =
  path i => com (j => A) 0 1 (p @ i) {
    i = 0 => x;
    i = 1 => q @ j
  }
```

`com` is atomic. Parenthesize compound caps; its cap includes postfix `@`
but not unparenthesized application. Tube bodies accept full expressions;
separate tubes with semicolons (a trailing semicolon is accepted). The face
is resolved in the surrounding dimension scope even if the composition binder
has the same spelling. See `examples/composition-surface.kamo` for path
concatenation and inversion.

Standalone compatible systems use `system A { face => value; ... }`. The type
argument includes postfix `@`; parenthesize compound types such as `A -> B`.
Each branch is checked at `A` under its face, including expected-type-directed
lambdas, paths, and matches. There is no additional dimension binder. Branches
must agree on overlaps and their faces must cover the current face context.
Unlike composition tubes, a system cannot leave the current context uncovered.
In particular, `i = 0 || i = 1` does not cover a generic Cartesian dimension.
Inside a composition tube, the enclosing face can justify a system that would
not cover the unrestricted context. Empty systems are accepted only under an
inconsistent face context. Faces use the same syntax and precedence as `com`.

```text
def eta (A : Type) (x : A) (y : A) (p : x == y) : x == y =
  path i => system A {
    i = 0 => x;
    i = 1 => y;
    top => p @ i
  }
```

See `examples/systems-surface.kamo` for total systems and systems local to
composition faces. Dependent pairs and projections below provide the equivalence
witnesses used by Glue.

Dependent pairs use `Sigma (x : A) => B`, where `x` binds a term variable
in `B`. Pair values are `(a, b)`; they require an expected Sigma type. The
first component is checked at `A`, and the second at `B[a/x]`, including
lambdas, matches, nested pairs, and paths. Named Sigma type families are unfolded
with fresh binders and bounded elaboration; the kernel still verifies conversion.
`fst p` has type `A`; `snd p` has type `B[fst p/x]`. Projections take a postfix
argument, so use `fst (f x)` for a compound application and `(fst p) @ i` to
apply a dimension to the projection result. Sigma bodies extend to the right;
parenthesize a Sigma type when using it as a function domain or argument.

```text
def packed : Sigma (A : Type) => A = (Bool, true)
def packedType : Type = fst packed
def packedValue : Bool = snd packed
```

Sigma universes use the maximum of the component levels. Pair values are
checked against expected types rather than inferred, so an unannotated
`let p = (a, b); ...` is not supported; pass a pair to a typed parameter or
use a typed definition. The new syntax lowers to existing `Sigma`, `Pair`,
`Fst`, and `Snd` terms. `examples/pairs-surface.kamo` includes dependent
packages, proofs about first components, and the kernel's `Fiber`, `Contr`,
`Equiv`, and identity-equivalence witness entirely in surface syntax.

Glue types use `Glue B { face => (A, equivalence); ... }`. On each face,
`A` is a type in the same universe as `B`, and the witness has the kernel's
existing equivalence type from `A` to `B`: a function with contractible fibers.
The elaborator supplies that type for inline pair/lambda witnesses; no specially
named library definition is required. Glue data must agree on overlaps, but
faces need not cover the whole context.

`glue G base { face => value; ... }` constructs an element of the explicit
Glue type `G`. Its elements must cover exactly the Glue domain in the current
context, agree on overlaps, and map to `base` under each equivalence's function.
Faces outside the Glue domain are rejected. `unglue G value` projects to the
base type. `G` may be an explicit Glue expression or a named type family exposed
by the existing bounded unfolding. Function and pair elements should use the
same faces as the corresponding type data to receive their expected types.
All arguments before braces are postfix expressions; parenthesize compound
applications, lambdas, and types. Glue forms introduce no new dimension binders.

```text
def ua (A : Type) (B : Type) (e : Equiv A B) : A == B =
  path i => Glue B { i = 0 => (A, e); i = 1 => (B, idEquiv B) }
```

`examples/glue-surface.kamo` defines the equivalence library, constructs this
map from equivalences to type paths, computes identity transport, and exercises
`glue`/`unglue` with full and empty domains. This example does not prove the
full univalence theorem. Glue terms lower to existing `Glue`, `GlueIntro`, and
`Unglue`; universe, equivalence, coverage, and coherence checks stay in the kernel.

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
- dependent pair types, pair values, and `fst`/`snd` projections;
- `let` expressions;
- homogeneous path equality, path abstraction, and dimension application;
- explicit dependent path types with `PathP`;
- transport along dimension-indexed type families with `coe`;
- heterogeneous composition with `com` and Cartesian face conditions;
- total compatible face systems with `system`;
- Glue types, element introduction, and projection (`Glue`, `glue`, `unglue`);
- surface declarations for parameterized and indexed inductive families;
- exhaustive constructor patterns for a single inductive family;
- explicit `return` motives and expected-type-directed matches, including dependent constructor refinement
  for ordinary indexed families, lowered to the core dependent eliminator;
- structural recursive calls lowered to the corresponding eliminator
  hypotheses.

Constructor arity, duplicate branches, family consistency, and exhaustiveness
are checked during elaboration. Structural recursion is restricted to calls
recognized through recursive constructor arguments; unrestricted recursion is
not accepted.

The `check-surface` and `normalize-surface` CLI modes load transitive file
imports. An import such as `import Data.Vec` resolves `Data/Vec.kamo` relative
to the importing module. Nested patterns, general match-result inference,
and general higher inductive types are not implemented.

## Universes

The checker currently has explicit **cumulative** universes:

```text
U i : U (i + 1)

A : U i    i <= j
-----------------
A : U j
```

Different universes are not definitionally equal. Cumulativity is implemented
as a separate checking/compatibility relation, without a runtime `Lift` term.

For dependent function and pair formation, the intended principal level is:

```text
level(Pi A B)    = max(level(A), level(B))
level(Sigma A B) = max(level(A), level(B))
```

Universe polymorphism and level inference are later work. See
[docs/universes.md](docs/universes.md).

## Inductive families

General inductive families are represented as checked core metadata rather than
being hidden entirely behind an encoding.

The current implementation includes:

1. checked inductive/constructor metadata;
2. generic family and constructor values;
3. dependent eliminators and iota computation;
4. surface `data` elaboration and ordinary constructor matching.

The core primitives remain for compatibility with the S-expression language,
but surface `Nat`, `Bool`, and `Vec` use the same generic inductive-family
metadata, eliminator, and iota computation as user declarations.
Generic composition is constructor-directed and covers dimensionwise-constant
direct-recursive, parameterized, and indexed examples. The generic parameter and
index lines—not merely their endpoints—must convert to both endpoints, and each
field composition must be provably constant. Varying or ambiguous cases remain
neutral rather than applying an unsound fallback.

Expected-type-directed surface matching elaborates to the existing dependent
eliminator. Distinct local-variable indices and a local-variable scrutinee are
abstracted from the expected result type. Constructor result indices and values
instantiate that motive in each branch; recursive arguments receive hypotheses
at their own indices and values. For example, structural copy of `Vec A n` can
return `Vec A n`, using the tail hypothesis at its smaller length.

Automatic motive synthesis is a conservative subset of dependent pattern
matching: compound or repeated indices are left fixed, with no equation solving or impossible-branch pruning.
Other local hypotheses are not generalized or rewritten. Matches still require
an expected result type and exhaustive flat constructor patterns.

An explicit elimination motive can be supplied with
`match value return (index1, ..., scrutinee => resultType) { ... }`.
Binders correspond to the family's indices in declaration order, then its
matched value; parameters remain fixed. For an unindexed type such as Nat,
only the value binder is supplied. Binders are distinct and scope over the
result type only, not the scrutinee or branches. Their dependent types come
from the family's checked metadata.

```text
def copySuccessor (A : Type) (n : Nat) (xs : Vec A (suc n)) : Vec A (suc n) =
  match xs return (length, value => Vec A length) {
    nil => nil A;
    cons k head tail => cons A k head tail
  }
```

Unlike automatic motive synthesis, this form can generalize compound and
repeated indices and expression scrutinees. Branches are checked against the
motive applied to each constructor's indices and value; recursive calls use
induction hypotheses at the recursive child's indices. The kernel checks that
the eliminator's result at the actual input matches the enclosing expected
type. All constructors still require branches: this does not solve index
equations or prune impossible cases. Flat constructor patterns and an expected
result type remain required; unannotated match inference is deferred.

Constructor applications now synthesize their full dependent function/result
types from metadata, supporting typed inference for `let xs = cons ...` and
matching constructor expressions directly. See `examples/match-motives-surface.kamo`.

## Higher inductive types

Kamo2 now includes a deliberately scoped first HIT milestone built on the
ordinary trusted representation, dependent elimination, and cubical composition
infrastructure. The supported surface declaration is:

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

A path constructor such as `loop` cannot be treated as an ordinary point
constructor. Its elimination rule needs boundary/coherence information and
should reuse Kamo's existing path/composition machinery.

The [higher-inductive design](docs/higher-inductive-types.md) specifies proposed
boundary metadata and staged implementation gates. Structurally and semantically
checked HIT signature staging has a gated one-dimensional core fragment for
higher applications, boundary reduction, dependent elimination, and scoped
unparameterized-Circle composition. The surface now accepts the exact
`data Circle` form with `base` and `loop : base == base`, including `loop @ i`
and endpoint computation. General parameterized/indexed/multidimensional HITs
and surface HIT matching remain unimplemented.

## Current core syntax

Definitions currently use:

```text
(def name type body)
```

Later definitions may refer to earlier definitions. `;` begins a line
comment.

| Form | Meaning |
| --- | --- |
| `(U level)` | Universe; checking is cumulative, while distinct universe levels remain definitionally unequal |
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
`bottom`, `(= r s)`, `(and phi psi)`, or `(or phi psi)`. The `and` and
`or` forms combine **face/cofibration formulas**; they are not interval
connections. Core interval expressions have no meet, join, or reversal
operation.

See [rule correspondence](docs/rules.md) for the current Cartesian cubical
theory, the distinction from De Morgan/CCHM interval structure, and the
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

A functional surface example demonstrates transport in both directions:

```sh
scripts/with-limits.sh target/release/kamo check-surface examples/transport-surface.kamo
scripts/with-limits.sh target/release/kamo normalize-surface examples/transport-surface.kamo forward
# true
scripts/with-limits.sh target/release/kamo normalize-surface examples/transport-surface.kamo backward
# false
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
- [x] non-dependent pattern matching and structural recursion lowering;
- [x] expected-type-directed dependent constructor refinement for ordinary indexed families;
- [x] explicit match motives for compound/repeated indices and expression scrutinees;
- [x] homogeneous cubical surface paths (`==`, `path`, `@`);
- [x] gated Circle HIT elimination and scoped composition;
- [x] scoped surface `data Circle` and higher path-constructor elaboration.

Next milestones:

- [ ] broader dependent pattern matching (index equations and nested patterns);
- [x] cubical transport surface syntax (`coe`);
- [x] explicit dependent path surface syntax (`PathP`);
- [x] cubical composition and face conditions (`com`, `=`, `&&`, `||`);
- [x] standalone compatible face systems (`system`);
- [x] surface dependent pairs and projections for equivalence witnesses;
- [x] Glue surface syntax (`Glue`, `glue`, `unglue`);
- [ ] generalize HIT declarations beyond the scoped Circle fragment.

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
