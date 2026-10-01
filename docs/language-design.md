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

This does not implement full dependent pattern matching. Compound or repeated
indices remain fixed; there is no index-equation solving, impossible-branch
pruning, or generalization of other dependent local hypotheses. Flat exhaustive
patterns and an expected result type are still required. Nested patterns and
general match-result inference remain future work.

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
broader dependent pattern matching
        |
        v
ergonomic cubical surface syntax
        |
        v
boundary-aware higher inductive types
```

The conservative ordinary-inductive composition rule is now part of the
boundary these later steps must preserve rather than an unimplemented milestone.

The governing constraint is that each step should remain compatible with the
Cartesian cubical core documented in [rules.md](rules.md).
