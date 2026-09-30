# Kamo2 language direction

This document records the intended direction of Kamo2. It is a design target,
not a claim that all features described here are implemented.

Kamo2 starts from Kamo's small cubical dependent core, but aims to grow into a
functional dependently typed language where ordinary programs, indexed data,
and cubical equality live in one language.

## Design principles

1. Keep the trusted cubical core small.
2. Put convenient functional syntax and elaboration above the core.
3. Treat equality as cubical paths rather than introducing a second equality.
4. Make inductive families a first-class design target before committing to a
   large pattern-matching language.
5. Add higher inductive types only after ordinary inductive families and their
   dependent eliminators are understood.
6. Prefer elaboration into a small set of core concepts over adding surface
   conveniences directly to the kernel.

The intended architecture is:

```text
functional surface syntax
        |
        v
name resolution / elaboration
        |
        v
inductive-family and cubical elaboration
        |
        v
small cubical dependent core
        |
        v
checker / evaluator
```

The existing S-expression language remains useful as a direct representation
of the core while the new surface language develops.

## Milestone 1: minimal functional surface language

The first surface language should be deliberately small. Its purpose is to make
later type-theoretic work readable, not to complete a general-purpose language
before inductive types are designed.

The initial target includes:

- named definitions,
- lambda abstraction,
- function application,
- dependent function types,
- non-dependent `A -> B` syntax,
- `let`,
- universes.

For example:

```text
def id (A : Type) (x : A) : A =
  x

def twice (A : Type) (f : A -> A) (x : A) : A =
  f (f x)
```

Surface syntax should elaborate to the existing `Pi`, `Lam`, and `App`
core constructs wherever possible.

Pattern matching, type classes, records, broad type inference, and syntactic
sugar are intentionally not goals of this milestone.

## Milestone 2: inductive types

The next goal is a representation for user-defined inductive declarations.

A desired declaration is:

```text
data Nat : Type where
  zero : Nat
  suc  : Nat -> Nat
```

The important result is not merely constructor syntax. An inductive declaration
must determine its constructors and a sound elimination principle.

Conceptually, `Nat` should provide an eliminator of the shape:

```text
Nat.elim :
  (P : Nat -> Type) ->
  P zero ->
  ((n : Nat) -> P n -> P (suc n)) ->
  (n : Nat) ->
  P n
```

Kamo currently has primitive `Nat`, `Bool`, and their eliminators. These may
remain as bootstrap/reference cases while the general inductive mechanism is
developed. Removing them from the core is a possible later simplification, not
an immediate requirement.

## Milestone 3: inductive type families

The first major language milestone is an indexed family such as `Vec`:

```text
data Vec (A : Type) : Nat -> Type where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)
```

This milestone forces the design to handle:

- parameters versus indices,
- constructor telescopes,
- positivity,
- universe levels,
- dependent eliminators,
- computation rules for eliminators.

`Vec` is a better architectural test than `List`: a design that handles only
non-indexed algebraic data is not yet sufficient for Kamo2.

The kernel boundary for general inductive families is an open design decision.
We should not assume that parsing a `data` declaration is enough. The trusted
representation, positivity checking, elimination rules, and computation rules
must be specified before general inductive families are accepted as kernel
features.

## Milestone 4: pattern matching

User-facing pattern matching should be built after dependent elimination is
available.

For example:

```text
def add : Nat -> Nat -> Nat
| zero,  n => n
| suc m, n => suc (add m n)
```

Pattern matching is intended to elaborate to elimination principles rather than
becoming an unrelated evaluator feature.

Dependent pattern matching will require substantially more care than ordinary
ML-style matching. In particular, matching on indexed constructors refines
indices and therefore affects the typing context.

Recursion should likewise preserve the normalization goals of the dependent
core. The initial direction is structural recursion / termination checking, not
an unrestricted fixpoint operator.

## Milestone 5: cubical surface language

Cubical structure should become visible when users work with equality, while
ordinary functional programs should remain ordinary-looking.

The intended equality notation is:

```text
x == y
```

with the meaning:

```text
Path A x y
```

rather than a separate inductive equality type.

Possible surface forms are:

```text
def refl (x : A) : x == x =
  path i => x

def cong (f : A -> B) (p : x == y) : f x == f y =
  path i => f (p @ i)
```

Here `path i => t` elaborates to path abstraction and `p @ i` to path
application.

Operations such as transport and composition should have readable surface
interfaces while elaborating to the existing cubical machinery. Low-level
dimension expressions should not leak into ordinary programs unnecessarily.

## Milestone 6: higher inductive types

Higher inductive types are a goal only after ordinary inductive families have a
clear trusted representation and elimination story.

The canonical test is the circle:

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

Unlike an ordinary constructor, `loop` is a path constructor. Supporting it
requires more than accepting this syntax: elimination must account for the
path constructor and its coherence/computation behavior.

Conceptually, eliminating from `Circle` requires data corresponding to both
the point constructor and a dependent path over `loop`.

Kamo's existing path, composition, coercion, and glue machinery should be
reused rather than creating a separate HIT runtime.

## Core versus surface

Kamo2 should avoid equating "surface feature" with "new kernel primitive."

Features expected primarily in the surface/elaborator include:

- multi-argument definitions and lambdas,
- arrow notation,
- `let`,
- pattern matching,
- convenient equality/path notation,
- inferred or implicit information where sound and useful.

Features whose trusted representation needs explicit design include:

- general inductive families,
- positivity and universe checking for data declarations,
- generated dependent eliminators and their computation rules,
- higher inductive constructors,
- HIT elimination and coherence.

This boundary should be documented before each feature is implemented.

## Development order

The working order is:

```text
minimal functional syntax
        |
        v
ordinary inductive declarations
        |
        v
inductive families: Vec / Fin
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

Two milestones act as architectural tests:

- **Vec milestone:** indexed dependent functional programming works without
  special-casing one family.
- **Circle milestone:** path constructors and their dependent elimination work
  using the cubical foundation.

In short: make `Vec` principled first, then make `Circle` principled.

## Near-term non-goals

Until the `Vec` milestone is understood, avoid committing to:

- a large ML/Haskell-style syntax,
- unrestricted general recursion,
- a separate propositional equality type,
- elaborate pattern syntax,
- aggressive global type inference,
- a permanent ABI/API for user-defined data declarations.

Keeping these decisions open gives the inductive-family and cubical designs room
to determine the language rather than being constrained by premature syntax.
