# Inductive families: core design sketch

This document narrows the language roadmap into an implementation direction for
ordinary inductive families. It is a design sketch for the `Vec` milestone,
not yet a kernel specification.

## Why this needs a core design

Kamo's current `Nat` and `Bool` are not merely parser conveniences.
They have dedicated syntax, semantic values, eliminators, and computation
behavior. Cubical composition also recognizes them.

A general `data` feature therefore cannot be treated as syntax sugar alone if
we want user-defined families to behave uniformly with the cubical evaluator.

The immediate goal is:

```text
data Vec (A : Type) : Nat -> Type where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)
```

without adding a `Vec` special case to the checker or evaluator.

## Options considered

### 1. Encode every inductive family using existing Pi/Sigma/path terms

This keeps the kernel smallest syntactically, but it has serious drawbacks.

- dependent elimination is not generally recovered by a simple Church encoding;
- positivity is hidden rather than represented and checked;
- computation behavior becomes encoding-dependent;
- the cubical evaluator currently needs structural knowledge of data for
  composition;
- the approach gives a poor foundation for later higher inductive types.

This may remain useful for experiments, but it is not the primary direction.

### 2. Generate ordinary global definitions for constructors and eliminators

This is attractive as an elaboration technique. However, some trusted component
still has to justify the generated eliminator and its computation rules.
Generating opaque declarations alone does not solve that problem.

We should use generated globals as a user-facing interface only if their
meaning is backed by checked inductive metadata.

### 3. Add checked inductive declarations to the core

This is the proposed direction.

A data declaration is checked once for well-formedness, positivity, universes,
constructor result indices, and other invariants. The core then retains a
compact description of the family and constructors.

Terms can refer generically to:

- an inductive family,
- one of its constructors,
- its eliminator.

The evaluator implements generic constructor/eliminator reduction from this
metadata rather than adding one Rust enum variant per user data type.

This increases the trusted core, but makes that increase explicit and
auditable. It also gives cubical composition access to the structure of an
ordinary inductive family.

## Proposed program-level representation

The exact Rust types are not fixed yet, but the core should distinguish ordinary
definitions from inductive declarations.

Conceptually:

```text
Program
  definitions : [Definition]
  inductives  : [InductiveDecl]

InductiveDecl
  name
  universe
  parameters : Telescope
  indices    : Telescope
  constructors : [ConstructorDecl]

ConstructorDecl
  name
  arguments : Telescope
  result_indices : [Term]
```

A telescope is an ordered dependent context:

```text
(x1 : A1) (x2 : A2 x1) ... (xn : An x1 ... x(n-1))
```

For `Vec`:

```text
parameters
  (A : Type)

indices
  (length : Nat)

nil.arguments
  []

nil.result_indices
  [zero]

cons.arguments
  (n : Nat)
  (head : A)
  (tail : Vec A n)

cons.result_indices
  [suc n]
```

Parameters are uniform across the family and its constructors. Indices may vary
between constructor results.

The core representation should use resolved IDs/de Bruijn references, not
surface names.

## Core term forms

A first implementation can introduce generic forms conceptually equivalent to:

```text
Inductive(inductive_id, parameters, indices)
Constructor(inductive_id, constructor_id, parameters, arguments)
Elim(inductive_id, motive, methods, scrutinee)
```

This is a sketch, not a commitment to eager argument vectors. Existing Kamo uses
curried `Pi` and `App`, so an implementation may instead expose family and
constructor constants whose semantic values accumulate applications.

The important invariant is that the evaluator can recover the inductive and
constructor identity without inspecting source syntax.

## Formation

For an inductive family

```text
D (p1 : P1) ... (pn : Pn) : (i1 : I1) -> ... -> (ik : Ik) -> Type u
```

the checker verifies:

1. parameter and index telescopes are well-typed in order;
2. the declared result is a universe;
3. each constructor type is well-typed;
4. each constructor ultimately returns `D` applied to exactly the declared
   parameters and a complete set of result indices;
5. recursive occurrences satisfy strict positivity;
6. universe constraints are satisfied.

Mutual inductive families are not part of the first milestone.

## Strict positivity

The first implementation should deliberately accept a conservative fragment.

Recursive occurrences of `D` are allowed only in positive positions. In
particular:

```text
D -> X
```

inside a constructor argument is negative and must be rejected when `D` is
the domain of that arrow.

For the initial `Vec` milestone, it is acceptable to support direct recursive
arguments first:

```text
tail : Vec A n
```

and postpone nested positivity such as `List (D ...)` until the variance of
referenced type constructors is represented.

Positivity is a trusted check, not a parser restriction.

## Universe levels

Kamo2 uses explicit cumulative universes as specified in
[`universes.md`](universes.md). Inductive declarations must use the same
compatibility judgment rather than inventing a separate lifting mechanism.

A declaration records its principal resulting universe level. Constructor
argument types must be valid at levels permitted by the formation rule, and a
type known at `U i` may be checked at `U j` when `i <= j`. This does not
make different universe levels definitionally equal and does not insert a
runtime `Lift` term.

The precise large-elimination policy remains a separate decision and must be
settled before dependent elimination is implemented. Universe polymorphism and
level inference are also later elaborator features; the first inductive
implementation may use explicit concrete levels.

## Dependent elimination

The eliminator is the central feature, not generated pattern syntax.

For `Vec`, the motive has the conceptual shape:

```text
P : (n : Nat) -> Vec A n -> Type
```

There is one method per constructor.

For `nil`:

```text
nil_case : P zero (nil A)
```

For `cons`, recursive constructor arguments additionally provide induction
hypotheses:

```text
cons_case :
  (n : Nat) ->
  (x : A) ->
  (xs : Vec A n) ->
  P n xs ->
  P (suc n) (cons A n x xs)
```

Then:

```text
Vec.elim :
  (P : (n : Nat) -> Vec A n -> Type) ->
  nil_case ->
  cons_case ->
  (n : Nat) ->
  (xs : Vec A n) ->
  P n xs
```

The exact implicit/explicit parameter presentation belongs to the surface
elaborator. The core rule should remain explicit.

## Iota computation

Elimination over a constructor must compute.

Conceptually:

```text
Vec.elim P nil_case cons_case zero (nil A)
  --> nil_case

Vec.elim P nil_case cons_case (suc n) (cons A n x xs)
  --> cons_case n x xs (Vec.elim P nil_case cons_case n xs)
```

This reduction belongs in the evaluator and is part of definitional equality.
It must not depend on a theorem proving propositional equality after the fact.

The generic evaluator should derive the recursive calls from constructor
metadata marking recursive arguments.

## Neutral elimination

When the scrutinee is neutral, elimination remains neutral while retaining
enough information for its type and for later reduction.

This mirrors the current treatment of applications and primitive eliminators:
normalization should reduce an eliminator exactly when the constructor becomes
known.

Quotation must also be extended so generic inductive values and stuck
eliminators round-trip into core syntax.

## Cubical composition

This is the main reason not to hide inductive structure behind an encoding.

The existing evaluator has composition behavior specialized for `Bool` and
`Nat`. A generic inductive family will eventually need analogous structural
composition.

For the first `Vec` implementation, separate two goals:

1. **dependent elimination milestone:** formation, construction, elimination,
   iota reduction, conversion, and quotation work;
2. **cubical stability milestone:** composition over user-defined inductive
   families is implemented and tested.

We should not claim full cubical support for a user-defined family after only
goal 1.

A likely generic strategy for ordinary strictly-positive constructors is to
preserve the constructor when compatible boundary data has the same constructor
shape and recursively compose its fields. Indexed families make this more
subtle because indices and dependent fields must remain coherent.

The exact composition rule requires a separate specification before coding it.

## Relationship to primitive Nat and Bool

Do not remove primitive `Nat` or `Bool` while building the generic system.

Instead, use them as reference implementations:

- compare generated `Nat` elimination with primitive `NatElim`;
- compare reduction behavior;
- compare quotation/conversion;
- later compare composition behavior.

Only after a user-defined `Nat` reaches the required behavior should we decide
whether the primitive variants can be removed.

This gives us differential tests during the transition.

## Surface elaboration

The surface declaration:

```text
data Vec (A : Type) : Nat -> Type where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)
```

should elaborate in stages:

```text
parse declaration
  -> resolve binders and names
  -> split parameters / indices
  -> check constructor result shape
  -> positivity check
  -> universe check
  -> create checked InductiveDecl
  -> expose family / constructor / eliminator names
```

Pattern matching is intentionally absent from this pipeline. It will later
compile to the generic eliminator.

## Implementation slices

The `Vec` milestone should be implemented in small independently testable
slices.

### Slice A: metadata only

Add internal IDs and checked representations for inductive declarations and
constructors. No new surface syntax yet. Unit tests construct metadata directly.

### Slice B: family and constructors

Add generic family/constructor core values, typing, evaluation, quotation, and
conversion. Test non-recursive data first, then a generic `Nat`.

### Slice C: dependent eliminator

Add motive/method checking, neutral elimination, and iota reduction. Reproduce
primitive `Nat` behavior and then test `Vec`.

### Slice D: declaration elaboration

Add minimal `data` syntax and elaborate it into checked metadata. Keep pattern
matching out.

### Slice E: cubical composition

Specify and implement composition for the supported inductive fragment. Add
path/composition tests for generic `Nat` and `Vec`.

Only after these slices should dependent pattern matching become the next major
feature.

## Initial restrictions

The first implementation may intentionally reject:

- mutual inductive definitions,
- nested inductive occurrences,
- higher-order recursive occurrences,
- higher inductive/path constructors,
- quotient-like constructors,
- unrestricted large elimination,
- general recursion.

These restrictions are preferable to accepting declarations whose positivity,
normalization, or cubical behavior is not justified.

## Path to HITs

The ordinary representation must leave room for constructors with boundaries,
but HIT support should not be faked as an ordinary constructor.

Later, a declaration such as

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

will require constructor metadata that can distinguish point constructors from
path/higher constructors and record their boundaries.

Its eliminator also requires coherence data for `loop`. Therefore the
ordinary `ConstructorDecl` proposed here should not be exposed as a permanent
public API until the HIT representation is designed.

The key architectural continuity is:

```text
checked declaration metadata
        +
generic elimination/computation
        +
cubical composition
        |
        v
ordinary inductive families
        |
        v
boundary-aware constructor metadata
        |
        v
higher inductive families
```

## Decision for the next implementation PR

Proceed with **checked inductive metadata in the core**, while keeping existing
primitive `Nat` and `Bool` unchanged.

Before Slice A, implement the cumulative-universe checking rules described in
[`universes.md`](universes.md). This prevents the inductive representation
from being designed around Kamo's old non-cumulative checking behavior.

After that universe change, the first inductive code PR should implement only
Slice A:

- `InductiveId` and `ConstructorId`;
- internal telescope/inductive/constructor metadata;
- storage in `Program`;
- validation-oriented unit-test fixtures;
- no parser syntax;
- no evaluator behavior change.

This gives us a concrete representation to review before increasing the trusted
checker/evaluator.
