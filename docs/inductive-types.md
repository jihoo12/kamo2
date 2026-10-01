# Inductive families

Kamo2 implements user-defined ordinary inductive families using checked core
metadata. This document describes the **current implemented fragment** and the
remaining cubical boundary.

For the exact cubical core rules, see [rules.md](rules.md). For universes, see
[universes.md](universes.md).

## Current representation

The core stores checked metadata for inductive declarations and constructors.
Surface `data` declarations elaborate into that metadata rather than becoming
one-off evaluator special cases.

Conceptually, a declaration contains:

```text
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

The implementation uses resolved core IDs and dependent telescopes rather than
surface names.

## What is implemented

The current implementation includes:

- checked inductive and constructor metadata;
- parameters and indices;
- generic family and constructor values;
- positivity and constructor-result validation for the supported fragment;
- dependent eliminators;
- iota computation for constructor scrutinees;
- neutral eliminators;
- quotation/conversion support;
- surface `data` declarations;
- ordinary constructor pattern matching elaborated above the core;
- trusted metadata validation before definition checking;
- conservative constructor-directed composition for non-indexed, parameterized,
  recursive, and indexed ordinary families.

This is enough to define and eliminate indexed families such as `Vec` without
adding a dedicated Rust variant for each user-defined family.

## Formation

For a family

```text
D (p1 : P1) ... (pn : Pn) :
  (i1 : I1) -> ... -> (ik : Ik) -> U u
```

the checker validates the parameter/index telescopes and constructor types,
requires constructor results to return the declared family with the appropriate
parameters and indices, applies the supported positivity discipline, and checks
universe constraints using the ordinary cumulative universe compatibility
relation.

Mutual inductive families, higher inductive constructors, and more permissive
forms of nested recursion are outside the current fragment.


## Strict positivity and trusted validation

The supported positivity fragment is deliberately conservative. A recursive
occurrence is accepted only when an entire constructor argument has the form
`D parameters indices`, with every parameter and index supplied and every
uniform parameter unchanged. Indexed direct recursion such as `tail : Vec A n`
is accepted. Negative occurrences such as `(D -> Nat) -> D`, nested occurrences
such as `List D`, and higher-order recursion are rejected.

This is a trusted-core rule rather than a surface-parser convention. Before any
ordinary definition is checked, the kernel revalidates metadata IDs and
ownership, de Bruijn scope, result-index arity, constructor result indices, and
the exact recursive-argument list. A semantic pass then checks that all
parameter, index, and constructor telescopes are types and that dependent result
indices inhabit their declared domains.

## Dependent elimination and iota computation

Elimination is a core operation backed by the checked metadata.

For a `Vec`-like family, the motive is conceptually:

```text
P : (n : Nat) -> Vec A n -> U u
```

and each constructor contributes one method. Recursive constructor arguments
receive induction hypotheses.

Elimination over a known constructor computes definitionally. For example:

```text
Vec.elim P nil_case cons_case zero (nil A)
  --> nil_case
```

and the `cons` case reduces to the corresponding method with recursively
computed induction hypotheses.

When the scrutinee is neutral, the eliminator remains neutral until evaluation
learns which constructor is present.

## Primitive Nat and Bool

Primitive `Nat` and `Bool` remain in the core. They are useful reference
cases for reduction and cubical behavior while the generic inductive subsystem
matures.

Their continued presence does not mean user-defined inductive families are only
surface encodings: generic families and eliminators are represented explicitly
in checked core metadata.

## Conservative generic cubical composition

User-defined ordinary inductives have constructor-directed composition for the
supported fragment. Reduction requires a known cap constructor and the same
constructor on every relevant nonempty tube. Uniform parameters must agree with
the source and target family, each dependent field domain must be definitionally
stable, and the constructor result indices reconstructed from the composed
fields must agree with the target indices. Direct recursive fields are composed
using the same generic rule.

If constructor shape is neutral or differs across a boundary, parameters vary,
or field/index coherence cannot be established by conversion, composition stays
as a neutral `Com`. This is intentionally not a general schema for nested
strictly-positive functors and is not a HIT composition rule.

## Relation to Cartesian cubical structure

Nothing in the inductive implementation adds De Morgan operations to the
interval. Dimensions remain endpoints or dimension variables, while
cofibrations are built separately from dimension equalities using face
conjunction/disjunction.

Any future composition rule for generic inductives must be stated against that
Cartesian structure rather than assuming interval meet, join, or reversal.

## Future extensions

The major remaining design areas are:

- richer positivity/nested-recursion policies;
- mutual inductive families;
- an explicit large-elimination policy;
- universe polymorphism;
- dependent pattern matching refinements;
- higher inductive constructors with boundary data and coherence.

Higher inductive types should extend the checked declaration representation with
boundary-aware constructor information rather than pretending path constructors
are ordinary point constructors.
