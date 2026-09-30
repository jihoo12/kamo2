# Universes

Kamo2 uses an explicit hierarchy of cumulative universes.

This document describes the intended checking discipline. Universe polymorphism
and level inference are later elaborator features; cumulativity itself belongs
to the type-checking relation.

## Hierarchy

For every level `i`:

```text
U i : U (i + 1)
```

Universes at different levels are not definitionally equal:

```text
U 0 != U 1
```

Cumulativity is instead a separate admissible checking relation:

```text
Gamma |- A : U i    i <= j
---------------------------
Gamma |- A : U j
```

Thus a type does not acquire a runtime wrapper or a `Lift` term when it is
used at a larger universe.

## Conversion versus cumulativity

Kamo currently checks many expected types through definitional conversion.
Kamo2 should not implement cumulativity by changing conversion so that universe
levels compare equal.

Conceptually, checking uses a compatibility/subtyping judgment:

```text
A == B
------
A <= B

i <= j
---------
U i <= U j
```

Initially this relation should stay deliberately small: definitional equality
plus universe cumulativity. It is not intended as a general-purpose subtyping
system.

This distinction matters for normalization and quotation: lifting a type from
`U i` to `U j` does not change the term being evaluated.

## Pi and Sigma

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

The surface non-dependent arrow `A -> B` is the same rule with an unused
binder.

The implementation should compute the principal level and rely on cumulativity
when a larger expected universe is requested.

## Paths

For a family

```text
i : I |- A i : U u
a0 : A 0
a1 : A 1
```

the path type remains in `U u`:

```text
Path A a0 a1 : U u
```

Using that path type at a larger universe is handled by the same cumulative
checking judgment. No special path-level lifting operation is introduced.

## Cubical operations

Kamo already evaluates composition in universes and implements `Glue`,
`coe`/composition, and paths. Cumulativity must therefore be introduced
without changing the semantic identity of a type.

The intended invariant is:

> universe lifting is a typing fact, not a new evaluated term.

In particular, adding cumulativity should not add a `Lift` constructor to
`Term` or `Val`.

Tests must cover paths, composition, and Glue at multiple universe levels so
that the checker change cannot silently invalidate cubical behavior.

## Inductive families

Inductive declarations are checked against the cumulative hierarchy.

For example, conceptually:

```text
data Vec (A : U i) : Nat -> U i where
  nil  : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)
```

A parameter inhabiting a smaller universe may be accepted where a larger
universe is expected through cumulativity.

The declaration records a principal resulting universe level rather than
materializing arbitrary lifted copies of the family.

The precise rules for large elimination remain a separate design decision and
must be specified before general inductive elimination is implemented.

## Universe polymorphism

Cumulativity does not by itself provide polymorphism over levels.

Eventually we want to express definitions conceptually like:

```text
id : (A : U i) -> A -> A
```

for a level variable `i`, rather than defining one `id` per concrete level.

That requires additional elaborator machinery:

- level variables/metavariables;
- level constraints such as `i <= j`;
- solving expressions involving `max` and successor;
- generalization of unsolved level variables where appropriate.

This is intentionally later work. The first cumulative implementation keeps
explicit concrete `u32` levels.

## Implementation order

Before inductive metadata is implemented:

1. introduce a small type-compatibility judgment distinct from conversion;
2. support `U i <= U j` when `i <= j`;
3. use compatibility when checking an inferred term against an expected type;
4. ensure Pi/Sigma formation returns `max(i, j)`;
5. add regression tests showing that `U i` and `U j` are still not
   definitionally equal;
6. add cubical regression tests across lifted universe usage.

After that, inductive metadata may assume cumulative universe checking.

Universe metavariables, level inference, and universe polymorphism should be
separate later changes.
