# Rule correspondence and implementation boundary

Specification: Angiuli, Brunerie, Coquand, Harper, Hou (Favonia), and Licata,
[Syntax and Models of Cartesian Cubical Type Theory](https://www.cs.cmu.edu/~rwh/papers/ccctt/preprint.pdf).
Section numbers below refer to that manuscript.

| Reference | Implementation |
| --- | --- |
| §§2.2–2.6: contexts, faces, substitution, equality | Separate term/interval environments and face assumptions; de Bruijn indices in syntax; unique semantic levels; exact positive equality reasoning subject to explicit resource limits |
| §2.7: composition and filling | `com`, with source/target equality and tube boundary reductions; `coe` is empty-tube composition; fillers compose to a fresh dimension |
| §2.8: dependent pairs | Dependent formation, beta/eta; composition transports the second component over the filler of the first |
| §2.9: dependent functions | Dependent formation, beta/eta; composition uses a backward filler for arguments |
| §2.10: dependent paths | Endpoint checking and reduction, path eta, composition with the two endpoint faces added |
| §2.11: Glue | Contractible-fiber equivalences, checked introduction boundaries and overlaps, unglue beta, Glue eta, weak introduction and extension of partial fiber data, followed by alignment using universally quantified faces |
| §2.12: universes | Numeric Russell universes, Glue-based universe composition, identity fiber contraction, and equivalence witnesses obtained by transporting identity-equivalence proofs |
| §§2.13–2.14: strict data | Primitive and generic ordinary inductives with dependent eliminators and conservative constructor-directed composition. Generic reduction requires a known common constructor, preserved parameters, definitionally stable field types, and coherent result indices. |

We do **not** implement Boolean or natural-number equality reflection. Empty
Glue is not definitionally collapsed to its base type, and transport in an
arbitrary constant type is not given an extra regularity rule. These shortcuts
would change the specified judgmental equality. Composition across neutral
types can remain blocked until substitution or stronger face assumptions expose
a reducible head.

Generic inductive declarations cross a kernel validation boundary before any
ordinary declaration is checked. The validator checks scoped and well-sorted
telescopes, constructor ownership, complete result indices, and exact recursive
argument metadata. Global aliases are rejected in positivity-relevant metadata,
so a transparent definition cannot hide a negative recursive occurrence. The
strict-positivity fragment permits only direct recursive arguments with
unchanged parameters; negative and nested occurrences are rejected.

Composition preserves a constructor only when all nonempty boundary pieces
expose that constructor, each generic parameter/index line converts to both
endpoints, and every field is provably constant along the composition. Equality
of the two endpoints is explicitly insufficient. Dependent fields are therefore
supported only in this constant fragment; otherwise composition remains neutral.

The interval remains Cartesian: dimensions are endpoints or variables, while
`and` and `or` combine face propositions. They are not interval meet/join, and
the kernel has no reversal, connections, or endpoint-enumeration principle.

## Cartesian interval structure versus De Morgan structure

Kamo's interval expressions are deliberately small:

```text
r, s ::= 0 | 1 | i
```

where `i` is a bound dimension name. Face/cofibration formulas are a separate
syntactic layer:

```text
phi, psi ::= top | bottom | (= r s) | (and phi psi) | (or phi psi)
```

The `and` and `or` operators above combine **face formulas**. They are not
De Morgan connections on interval expressions. In particular, the core has no
interval terms corresponding to `i ∧ j`, `i ∨ j`, or interval reversal
`~i`/`1-i`.

This distinction is semantically significant. A generic interval dimension is
not treated as Boolean: `(= i 0) or (= i 1)` does not entail `top`. Diagonal
faces such as `(= i j)`, equality transitivity, dimension substitution, and
generic-dimension quantification are handled directly by the Cartesian face
solver.

Operations that are often written using interval connections or reversal in a
De Morgan/CCHM presentation must therefore be built using the Cartesian
composition primitives available here. For example, the library's path
symmetry construction uses composition rather than an interval-reversal term.

References to Cubical Agda below concern proof/construction patterns. They do
not mean that Kamo imports Cubical Agda's De Morgan interval algebra.

## Computational univalence

The library uses the ordinary definition

```
Fiber f b = Sigma a A (Path i B (f a) b)
Contr A   = Sigma center A (Pi point A (Path i A center point))
Equiv A B = Sigma f (Pi a A B) (Pi b B (Contr (Fiber f b)))
```

`ua` is a Glue path with the supplied equivalence at the first endpoint and
the identity equivalence at the second. It is an ordinary definition, not a
kernel primitive. Boolean negation's equivalence witness is proved by filling
its fibers using the two involution homotopies.

The full theorem proceeds by proving contractibility of `Sigma A (U 0)
(Equiv A B)`, using the equivalence of `unglue`. It obtains a decoding path,
proves a section by dependent composition, and proves a retraction by singleton
path induction. The checked isomorphism-to-equivalence lemma then constructs a
contractible-fiber witness for the canonical map.

Two formulations are named explicitly:

- `transport-equiv`: its forward function is transport along a universe path.
- `path-to-equiv`: the canonical map defined by transporting the identity
  equivalence backwards in the domain family `Equiv (p i) B`.

`univalence` proves that **`path-to-equiv` is an equivalence**, with domain
`Path i (U 0) A B` and codomain `Equiv A B`. This domain is in `U 1`, which is why
the explicit library has a mixed-level `Equiv10` definition. The implementation
does not silently equate universe levels.

The geometric isomorphism and equivalence-extension constructions also follow
the standard methods illustrated in the Cubical Agda library's
[Isomorphism](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Isomorphism.agda)
and [Univalence](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Univalence.agda)
modules. Kamo's terms use Cartesian composition with explicit source/target
dimensions; they do not import Agda's De Morgan connections or interval reversal.

## Evaluation and allocation

The kernel uses a graph-based form of normalization by evaluation: syntax
suspensions carry explicit environments, and semantic binders carry unique
levels and delayed substitutions. Beta reduction instantiates binders without
substituting through source syntax. Values, environments, substitutions, and
faces have separate typed arena IDs. Public checked programs retain only syntax.

Optimized substitution composition builds a graph; it does not eagerly copy
the images of every earlier substitution. Forcing pushes substitutions only as
needed. Interning and unfolding caches preserve sharing. A bounded congruence
check exposes ordinary beta redexes before expanding Kan operations, avoiding
large expansions when the same computation occurs on both sides of an equality.
Failure of that shortcut falls through to typed conversion.

Reduction caches are keyed by value, face context, and whether the caller needs
the underlying Glue data. Glue composition retains its exposed type data:
re-evaluating the original type after substitution could otherwise lose that
data by reducing to a boundary type. Caches and semantic arenas are discarded
between declarations and between normalization calls.

Face nodes are shared. Entailment compares normalized disjunctions of equality
partitions, checking transitivity and the inconsistency of `0 = 1`. A generic
fresh dimension, rather than endpoint enumeration, implements universal face
quantification. Intermediate expansion and solver caches are bounded.

The performance-oriented [cctt notes](https://github.com/AndrasKovacs/cctt)
motivated delayed substitution and demand-driven computation. Kamo does not
adopt its restriction on disjunctive systems or its closed-evaluation shortcuts
that require a different canonicity invariant.

## What the checks establish

Tests validate the complete library theorem, concrete transports, invalid
boundaries/equivalences/universes, capture avoidance, substitution composition,
context-sensitive cache behavior, arena disposal, and resource errors. Generated
Boolean computations are also compared with an independent Boolean oracle.
Optimized and reference execution are compared on computation examples.

The two execution modes share the mathematical reduction code. Their agreement
does not independently validate those rules. Native semantic expansions of
derived constructions remain part of the trusted implementation; the identity
fiber construction is additionally compared against its checked library term.
Passing the library is evidence about this implementation, not a mechanized
proof of kernel soundness or normalization. Resource-bounded conversion may
report an inconclusive result for a valid term.
