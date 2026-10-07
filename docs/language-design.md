# Kamo2 language direction

This document is a **future roadmap**. For implemented behavior and the trusted
core boundary, use [../README.md](../README.md) and [rules.md](rules.md) as the
source of truth.

Kamo2 starts from a small Cartesian cubical dependent core and aims to grow into
a functional dependently typed language where ordinary programs, indexed data,
and cubical equality share one coherent elaboration pipeline.

## What already exists

The current system already has:

- a functional surface syntax with typed definitions, functions, and `let`;
- file modules, imports, and name resolution;
- surface `data` declarations for parameterized and indexed families;
- checked indexed-inductive metadata with conservative trusted positivity validation;
- generic dependent eliminators and iota computation;
- expected-type-directed constructor matching with dependent index/value
  refinement and structural-recursion lowering;
- conservative constructor-directed composition for the dimensionwise-constant
  ordinary-inductive fragment;
- homogeneous surface path equality (`==`), path abstraction (`path`), and
  dimension application (`@`), elaborated to existing core paths;
- surface transport `coe (i => A) r s value`, lowered to existing core
  composition with no tubes and checked at the source and destination types;
- explicit dependent paths `PathP (i => A) left right`, with endpoint-directed
  checking, type-family instantiation for `@`, and existing core `Path` lowering;
- surface composition with scoped tubes and Cartesian face equalities,
  conjunction, and disjunction, checked by the existing core;
- standalone compatible systems with contextual coverage and overlap checks;
- dependent pairs (`Sigma`), pair values, and projections (`fst`, `snd`);
- surface Glue types, introduction, and projection with existing kernel checks;
- explicit elimination motives and full constructor-application type synthesis;
- exhaustive disjoint nested constructor patterns lowered to flat eliminations;
- result type synthesis for explicit-motive matches in unannotated contexts;
- expression type ascriptions and typed lets with expected-type propagation;
- cumulative explicit universes;
- the Cartesian cubical core: paths, composition/coercion, systems, and Glue.

These are current implementation facts, not future milestones.

## Design principles

1. Keep the trusted cubical core small and auditable.
2. Put ergonomic syntax, name resolution, and elaboration above the core.
3. Use cubical paths as the language's equality notion rather than adding an
   unrelated propositional equality primitive.
4. Extend inductive families only with rules whose positivity, computation, and
   cubical behavior can be stated precisely.
5. Add higher inductive types only while preserving the explicit
   ordinary-inductive composition and dependent-elimination boundary.
6. Prefer elaboration into a small core over adding convenience features as
   kernel primitives.

The architectural direction remains:

```text
functional surface syntax
        |
        v
name resolution / elaboration
        |
        v
inductive + cubical elaboration
        |
        v
small Cartesian cubical dependent core
        |
        v
checker / evaluator
```

## Cubical foundation

Kamo2's interval syntax is Cartesian, not a De Morgan interval algebra.

Core dimensions are endpoints or bound dimension names. Conjunction and
disjunction live in the separate face/cofibration language; they are not
interval connections. There is no core interval meet, join, or reversal
operation.

See [rules.md](rules.md) for the precise distinction and the correspondence
between the implementation and the Cartesian cubical rules.

## Near-term work

### Preserve the ordinary-inductive boundary

Generic constructor-directed composition is now implemented for a deliberately
conservative ordinary-inductive fragment. It reduces only when constructor
shape is known and common across the boundary, each generic parameter/index
line is definitionally constant across the composition, and every constructor
field is proved constant enough for later dependent fields and result indices.

Equal endpoints alone are not sufficient. Genuinely varying or ambiguous
parameter, index, or dependent-field cases remain neutral `Com` values rather
than being reconstructed with an unsound fallback.

Near-term kernel work should keep this boundary explicit. Richer dependent
structural composition or support for nested strictly-positive functors should
only be added together with precise filler/coherence rules for the Cartesian
interval structure.

### Dependent pattern matching

Expected-type-directed dependent constructor refinement now exists for ordinary
indexed families. The elaborator abstracts distinct local-variable indices and
a local-variable scrutinee from the surrounding expected result type, under fresh
binders. Each branch uses the constructor's result indices and constructed value;
each recursive hypothesis uses its argument's own indices and value. The result
is an existing checked generic eliminator, with no new kernel matching rule.

Automatic synthesis does not implement full dependent pattern matching. Compound or repeated
indices remain fixed; there is no index-equation solving, impossible-branch
pruning, or generalization of other dependent local hypotheses. Exhaustive
patterns and an expected result type are required for automatic motives.
Branch-based inference without an explicit motive remains future work.

Explicit motives use `match value return (indices..., scrutinee => resultType)`
before the branch block. Index binders are ordered as in the family's metadata,
followed by one value binder. Parameters remain fixed. Binders are distinct,
have metadata-derived dependent types, and scope only over the result type.
The motive is lowered to the same kernel eliminator as automatic matches;
constructor branches and recursive hypotheses instantiate it at their own
indices and values. Compound and repeated indices and non-variable scrutinees
can be generalized explicitly. Exhaustive patterns are still required; equation
solving and impossible-branch pruning remain deferred. Constructor applications
now synthesize their full dependent types from checked metadata, enabling
inference for let-bound constructors and expression scrutinees.
See `examples/match-motives-surface.kamo`.

Explicit-motive matches synthesize a type by reifying their motive at the actual
indices and matched value. The reification environment carries metadata-derived
types for index expressions and the known scrutinee type. Inner term and dimension
binders are freshened by core decoding before arguments are inserted, avoiding
capture in dependent function, pair, and path types. This supplies types for
unannotated lets, function positions, and projections while retaining the same
kernel branch and eliminator checks. Branch-based inference without a motive is
not implemented. See `examples/inferred-match-surface.kamo`.

Nested constructor arguments use parentheses: `suc (zero)` and `suc (suc k)`.
The elaborator groups outer constructors, chooses inspected argument columns,
and compiles complete disjoint rows into flat matches. Each generated match
uses existing exhaustive-constructor validation and dependent motive synthesis.
No kernel representation or equality rule changes. Binder substitution respects
all nested pattern binders. Overlaps, duplicate binders, missing constructors,
and mixed variable/constructor rows at a selected split are rejected; no
ordered fallback or equation solving is added. Self recursion is rejected inside
nested-pattern matches because an inner elimination hypothesis is not generally
the enclosing function's hypothesis. Flat structural recursion remains available.
Decision-tree depth is bounded at 128 splits. See
`examples/nested-patterns-surface.kamo`.

Expression ascriptions `(value : type)` and typed lets
`let name : type = value; body` expose the existing core annotation mechanism.
Typed lets wrap their values in annotations and reuse ordinary let lowering;
the declared type checks the value and guides uninferable lambdas, pairs,
paths, and matches. The kernel checks annotations even in unused bindings.
Dependent Pi binders retain priority for `(x : A) -> B`; ascribed domains use
`((x : A)) -> B`. The let name scopes over the body only. Function and path
aliases use bounded unfolding for expected-type propagation and application.
Let lowering prefers a synthesized body codomain, allowing it to depend on the
bound value, and falls back to the surrounding expected type for uninferable
bodies. Pair projection reduction is supported by the bounded type-head
exposure used in elaboration. See `examples/annotations-surface.kamo`.

### Cubical surface syntax

The first ergonomic cubical surface slice is implemented:

```text
x == y
path i => t
p @ i
p @ 0
p @ 1
```

`==` denotes homogeneous, constant-family path equality. Its family is inferred
from the left endpoint and both endpoints are checked by the kernel. The family
is lowered under a fresh anonymous dimension binder so outer dimension references
are preserved. `path` uses expected-type-directed checking and lowers to `PLam`;
`@` lowers to `PApp`. Dimensions have their own lexical scope and are never term
variables. No kernel semantics are added.

Precedence is postfix `@`, then application, then non-associative `==`, then
right-associative `->`. For example, `f x == g y` compares two applications;
`f p @ i` means `f (p @ i)`. Use `(f x) @ i` to apply a dimension to a function
result. Chained equalities require parentheses.

Transport is written `coe (i => A) r s value`. The dimension binds only the
family `A`, not `r`, `s`, or `value`. The elaborator supplies `A[r/i]` as the
expected type of the value (including lambdas and matches), and synthesizes
`A[s/i]` for the result. Lowering uses the existing `Com` term with no tubes;
source/destination typing and computation remain the kernel's responsibility.
In particular, neutral type lines are not treated as constant just because
their endpoints agree. See `examples/transport-surface.kamo` for a runnable
example and the README for argument precedence.

Explicit dependent paths use `PathP (i => A) left right`. The family alone
binds `i`; endpoints are checked at `A[0/i]` and `A[1/i]`. A path abstraction
checks its body at the family instantiated with its own dimension, and path
application synthesizes the family at the supplied dimension. Core-to-surface
metadata reconstruction preserves the family instead of assuming homogeneity.
The kernel's existing metadata restrictions still reject dimension application
inside inductive constructor argument types. See
`examples/dependent-paths-surface.kamo` for paths built from transport and a
varying family of identity functions.

Composition uses `com (i => A) r s cap { face => tube; ... }`. Its binder
scopes over the family and tube bodies only. Faces use `top`, `bottom`,
dimension equality `=`, conjunction `&&`, disjunction `||`, and parentheses,
with equality tighter than conjunction and conjunction tighter than disjunction.
The elaborator resolves faces before entering the composition scope and provides
the family as the expected type of tube bodies. It lowers directly to `Com`;
the kernel retains responsibility for source compatibility and overlap coherence.
No coverage requirement is added for composition tubes. The Cartesian path
concatenation and inverse examples in `examples/composition-surface.kamo` require
neither interval connections nor reversal.

Standalone compatible systems use `system A { face => value; ... }`. Branch
bodies receive the annotated type as their expected type, and lowering uses
existing core `System` terms. There is no new dimension binder. The kernel
checks agreement on overlaps and coverage of the current face context. A system
inside a composition tube can use that tube's face restriction; endpoint faces
alone do not cover a generic Cartesian dimension. Empty systems require an
inconsistent context. See `examples/systems-surface.kamo`.

General path-abstraction inference remains future work. Dependent pairs are now available as `Sigma (x : A) => B`, with pair values
`(a, b)` and projections `fst` and `snd`. The second component checks against
`B[a/x]` with the first component's known type retained for elaboration of
uninferable terms such as lambdas. Projections synthesize the domain and the
codomain instantiated with `fst p`. Named type families are decoded with fresh
binders and exposed by bounded unfolding and beta reduction. The kernel retains
all universe, conversion, and dependent-pair computation checks. Pair values
require expected Sigma types; unannotated pair inference is deferred.
`examples/pairs-surface.kamo` constructs an identity equivalence witness,
providing the witnesses used by surface Glue.

Glue uses `Glue B { face => (A, equivalence); ... }`, with introduction
`glue G base { face => value; ... }` and projection `unglue G value`.
The elaborator supplies the kernel's map-with-contractible-fibers type for
witnesses and known face-specific types for elements, then lowers directly to
existing core terms. No library name is privileged. Type data need not cover
all faces; elements must cover the Glue domain, remain inside it, and have
compatible images and overlaps. Named Glue families use bounded unfolding,
with their faces preserved during core-to-surface reconstruction.
`examples/glue-surface.kamo` constructs the map from equivalences to paths and
verifies identity transport; it does not establish the full univalence theorem.

Only endpoints and bound names are dimensions: there is no
surface or core interval meet, join, or reversal. The scoped Circle higher
constructor described below is now implemented; broader HIT syntax remains later
work.

### Higher inductive types

A scoped first higher inductive milestone is now implemented. The declaration:

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

is accepted when it has exactly this unparameterized/nullary point-plus-path
shape. `loop` is elaborated through checked higher metadata and path application,
not treated as an ordinary point constructor. Ordinary surface `match` on Circle
remains rejected because it cannot state the required coherence method.

Parameterized/indexed/multidimensional HIT declarations and general HIT matching
remain later work. The existing Cartesian path, composition, coercion, and Glue
machinery remains the foundation for those extensions.

### Universe polymorphism

Universe checking is cumulative today, but levels are explicit concrete
integers. Level variables, inference, constraint solving, and generalized
universe-polymorphic definitions are elaborator work for a later stage.

## Non-goals for the near term

The project should avoid making the trusted core larger merely to obtain:

- unrestricted general recursion;
- a second equality primitive unrelated to cubical paths;
- broad global type inference;
- convenience-only syntax that can instead elaborate to existing constructs;
- higher inductive syntax without a specified boundary/composition/elimination
  story.

The next architectural tests are therefore:

```text
broader dependent pattern matching
        |
        v
further cubical surface syntax
        |
        v
boundary-aware higher inductive types
```

The conservative ordinary-inductive composition rule is now part of the
boundary these later steps must preserve rather than an unimplemented milestone.

The governing constraint is that each step should remain compatible with the
Cartesian cubical core documented in [rules.md](rules.md).
