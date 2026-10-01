# Kamo2 language direction

This document is a **future roadmap**. For implemented behavior and the trusted
core boundary, use [../README.md](../README.md) and [rules.md](rules.md) as the
source of truth.

Kamo2 starts from a small Cartesian cubical dependent core and aims to grow into
a functional dependently typed language where ordinary programs, indexed data,
and cubical equality share one coherent elaboration pipeline.

## What already exists

The current system already has:

- a functional surface syntax;
- file modules and name resolution;
- surface `data` declarations;
- checked indexed-inductive metadata;
- generic dependent eliminators and iota computation;
- ordinary constructor pattern matching;
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
5. Add higher inductive types only after ordinary inductive composition and
   dependent elimination have a clear specification.
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

### Generic cubical composition for inductive families

User-defined inductive families already support formation, constructors,
dependent elimination, and iota computation, but they do not yet have generic
structural composition.

This is the most important remaining kernel-facing step before claiming that
ordinary user-defined data has the same cubical stability as the primitive
`Nat` and `Bool` cases.

The rule must account for constructor shape, recursive fields, indices, and
dependent fields without assuming De Morgan interval operations.

### Dependent pattern matching

Ordinary constructor matching exists. The next pattern-matching work is
dependent refinement: matching an indexed constructor changes what is known
about indices in the branch context.

This should elaborate to checked elimination principles rather than become an
independent evaluator mechanism.

### Cubical surface syntax

The core cubical operations exist, but their surface presentation can become
more readable.

A target notation is conceptually:

```text
x == y

path i => t

p @ i
```

where equality elaborates to `Path`, path abstraction to the core path
lambda, and path application to the existing path application form.

Transport and composition should likewise gain readable interfaces without
forcing low-level dimension syntax into ordinary functional code.

### Higher inductive types

Higher inductive types remain a later goal. A declaration such as:

```text
data Circle : Type where
  base : Circle
  loop : base == base
```

requires boundary-aware constructor metadata and elimination/coherence rules;
it must not be treated as an ordinary point-constructor extension.

The existing Cartesian path, composition, coercion, and Glue machinery should
remain the foundation for this work.

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
generic inductive composition
        |
        v
dependent pattern refinement
        |
        v
ergonomic cubical surface syntax
        |
        v
boundary-aware higher inductive types
```

The governing constraint is that each step should remain compatible with the
Cartesian cubical core documented in [rules.md](rules.md).
