# Universes

Kamo2 has an explicit hierarchy of **cumulative** universes.

This document describes the behavior implemented by the current checker. It is
not a proposal for changing definitional equality, and it does not introduce a
runtime lifting operation.

## Hierarchy

For every level `i`:

```text
U i : U (i + 1)
```

Universes at different levels are not definitionally equal:

```text
U 0 != U 1
```

Cumulativity is a separate checking/compatibility relation:

```text
Gamma |- A : U i    i <= j
---------------------------
Gamma |- A : U j
```

The implementation reflects this separation: conversion remains ordinary
definitional equality, while compatibility additionally accepts `U i` where
`U j` is expected when `i <= j`.

There is no `Lift` term or runtime wrapper.

## Formation levels

If

```text
Gamma |- A : U i
Gamma, x : A |- B : U j
```

then:

```text
Gamma |- (x : A) -> B : U (max i j)
Gamma |- (x : A) *  B : U (max i j)
```

A path family in `U u` forms a path type in `U u`.

The checker computes these principal levels and relies on universe compatibility
when a term is checked against a larger expected universe.

## Cubical operations

Universe cumulativity does not change Kamo2's Cartesian cubical semantics.
Paths, composition, coercion, systems, and Glue continue to evaluate using the
same core terms and values regardless of the larger universe in which a type is
accepted.

The invariant is:

> universe lifting is a typing fact, not a new evaluated term.

Regression tests cover cumulativity together with path, composition, and Glue
behavior and separately verify that distinct universe levels have not become
definitionally equal.

## Inductive declarations

User-defined inductive declarations use the same cumulative checking relation as
the rest of the core. They do not have a separate universe-lifting mechanism.

The current implementation supports explicit concrete universe levels. The
family records a principal result level, and constructor types are checked
against the declaration using the ordinary checker.

Large-elimination policy for future extensions should be specified separately
rather than being inferred from cumulativity alone.

## Future work: universe polymorphism

Cumulativity is not universe polymorphism. Kamo2 does not yet provide level
variables, level inference, or generalized universe-polymorphic definitions.

A future elaborator may support definitions conceptually like:

```text
id : (A : U i) -> A -> A
```

with machinery for:

- universe level variables and metavariables;
- constraints such as `i <= j`;
- `max` and successor constraints;
- generalization of unsolved level variables.

That work should preserve the current separation between definitional equality
and cumulative checking.
