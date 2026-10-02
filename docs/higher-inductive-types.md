# Higher inductive types: trusted representation and Circle plan

Status: **design only; no HIT metadata or executable HIT semantics implemented**.
This proposal uses Circle to fix the trusted representation before implementing
evaluation, elimination, composition, or surface HIT declarations. Ordinary
inductives and homogeneous surface paths are implemented; they do not already
provide higher constructors. No runtime behavior changes with this document.

## Existing boundary and required audit obligations

The source of truth remains [rules.md](rules.md),
[inductive-types.md](inductive-types.md), and the
[pre-HIT audit and dimension-varying follow-up](kernel-audit.md#pre-hit-ordinary-inductive-audit--2026-10-01).
The [language roadmap](language-design.md) describes future surface features.
This design was checked against `src/syntax.rs`, `src/check.rs`, `src/eval.rs`,
`src/face.rs`, `src/surface/ast.rs`, and `src/surface/elaborate.rs`.

In particular:

- `Program::validate_inductives` checks ordinary structural metadata;
  `Engine::check_inductive_declarations` checks sorts and dependent indices.
  Neither validates a higher boundary. The ordinary metadata grammar excludes
  global aliases and most executable terms. Its term-scope traversal is not a
  dimension-aware boundary validator.
- `Term::Constructor` / `Val::Constructor` denote point constructors, applied
  through ordinary term application. Generic `Elim` methods follow the family's
  point-constructor list and derive recursive hypotheses from checked metadata.
- `compose_inductive` requires a common constructor, generically constant
  parameters/indices, stable dependent domains, and provably constant fields.
  Equal endpoints alone are insufficient. This rule is not a HIT rule.
- `Term::Path` has a dimension binder in its family, but not in its endpoints;
  `PLam` binds a dimension and `PApp` applies one. Surface `==` creates only a
  constant-family path. Dependent core paths already exist.
- Syntactic dimensions `D` are `Zero`, `One`, or `Bound(usize)`; semantic
  dimensions `Dim` use fresh levels. Faces `F` use equality, conjunction, and
  disjunction. Neither the syntax nor the solver supplies interval connections,
  reversal, or a principle that all dimensions are endpoints.

The audit's four remaining blockers are requirements: checked boundaries
(Slices A/B), eliminator coherence (D), a separately justified HIT composition
schema (E), and explicit acknowledgment that testing is not a mechanized
metatheory. Nothing here discharges the last requirement by analogy to a
De Morgan cubical implementation. The earlier substitution/face audit also
requires reduction and conversion to remain stable under simultaneous
substitution of terms, dimensions, and faces.

## Representation decision

Choose **separate point and higher constructor records and ID spaces**, with a
single ordered, tagged membership list on a HIT family. The following is a
proposed schema, not Rust added by this change:

```text
ConstructorRef = Point(ConstructorId) | Higher(HigherConstructorId)

FamilyConstructors =
  Ordinary(Vec<ConstructorId>)
  | Higher(Vec<ConstructorRef>)

HigherConstructorDecl {
  id: HigherConstructorId,
  inductive: InductiveId,
  name: String,
  arguments: Telescope,
  dimensions: DimensionTelescope, // ordered binder labels, no term types
  result_indices: Vec<TermId>,
  boundary: PartialConstructorBoundary,
}

PartialConstructorBoundary {
  pieces: Vec<BoundaryPiece>,
}
BoundaryPiece { face: F, term: TermId }
```

`Program` would gain a higher-constructor table. The current `ConstructorDecl`
remains the point record, including its ordinary recursive annotations.
`InductiveDecl.constructors` would become `FamilyConstructors`; it must not
retain an independently authoritative point-only list alongside a HIT list.
Point methods and higher methods use the tagged declaration order. Names are
diagnostics/resolution aids; IDs and validated membership establish identity.
The family tag is checked against its members, not trusted as a caller promise.
For the first fragment a `Higher` family must contain at least one higher member.

| Candidate | Merits | Tradeoff / decision |
| --- | --- | --- |
| Separate records and IDs, tagged family membership | A higher ID cannot enter `Term::Constructor`; the ordinary metadata and recursion contract stay explicit; family dispatch must acknowledge HITs | Selected. Requires two tables and validation of the combined membership/order |
| One `ConstructorId` table with `ConstructorDecl::Point` / `::Higher` | Viable: exhaustive matching can enforce the distinction, and ordering/ownership use one table | Not selected: every consumer of the existing ID and constructor term would need a variant check; accidentally treating a higher ID as a point head becomes a trusted runtime concern |
| Add optional dimensions/boundary to the ordinary record, or encode `loop` as a fieldless point / function returning a path | Superficially fewer changes | Rejected: admits ambiguous states, conflates term and dimension application, and invites point iota/composition to ignore boundaries |

The separate representation is selected for its invariants, not its migration
cost. Changing family dispatch is deliberate: **all ordinary-only consumers
must reject a Higher family**, including ordinary `Elim`, surface pattern
matching/exhaustiveness, and ordinary structural composition. This applies even
when the current value is its point constructor `base`. Future HIT elimination
may share point-method helpers, but it cannot request only the point methods.

Raw candidates, structurally validated candidates, and semantically checked
signatures must be distinct API states. Only the last state can later authorize
HIT terms. Slice A metadata must remain in a staging container excluded from
`CheckedProgram` execution; it is not a certificate of a new type. Publication
is atomic after validation, with no mutable metadata behind the certificate.

## Scope convention and initial fragment

Use independent term and dimension scopes. Family parameters and indices retain
the ordinary closed telescope convention. A constructor does **not** bind the
family's index telescope as locals: it supplies result indices instead.

For parameters `p1 ... pn`, constructor arguments `a1 ... am`, and dimensions
`i1 ... ik`, the scope order is:

```text
parameters ; arguments ; dimensions
term locals: p1 ... pn a1 ... am
dimension locals: i1 ... ik
```

Argument `aj`'s type sees the parameters and preceding arguments, with no free
constructor dimensions. Dimensions are independent Cartesian binders, not
values of a new interval type or entries in a term `Pi` telescope. Result
indices and all boundary faces/terms see all arguments and dimensions. In the
full constructor scope `Var(0) = am` and `D::Bound(0) = ik`. At argument `aj`,
parameter `pl` has term index `n + j - l - 1` (positions start at one).
Under a nested path binder outer dimension indices shift, while term indices
do not; under a term binder the converse holds. This convention intentionally
does not support interleaved dimension-dependent argument telescopes.

The initial executable target is the **nonrecursive one-dimensional fragment**,
including Circle. Metadata can describe full cubical boundaries in more
dimensions, but that does not authorize their evaluation/elimination. Capability
checks must reject unsupported dimension counts at each executable entry point.
Parameters, nonrecursive arguments, and indices have the above storage convention
even if the first end-to-end tests use empty telescopes.

For the initial metadata acceptance policy, exclude occurrences of the family
being defined from parameter/index domains, argument types, and result-index
expressions, including negative, nested, and direct recursive arguments. Apply
this nonrecursive restriction to point members of a Higher family as well.
Ordinary families retain their existing direct-recursion fragment unchanged.
No recursive-argument annotations are accepted on a higher record.

Boundary terms initially have a deliberately small grammar: a fully applied
earlier point constructor of the same owner, with uniform parameters and
well-scoped nonrecursive arguments. Its fields and the telescopes/indices use
the existing conservative metadata term grammar, with full ID checks and no
globals; current-family occurrences are forbidden in those fields. Thus
`base` is allowed, but eliminators, arbitrary globals, `Com`, nested current-
family structure, self references, and earlier higher constructors are not.
This is a syntactic whitelist, not a claim that everything well-typed is an
admissible boundary. It permits semantic validation before higher term semantics
exist. Expanding the grammar later requires bounded reference traversal and a
new coherence review. The `TermId` storage need not change to admit checked
earlier higher applications after Slice C; their declaration dependency graph
must remain acyclic. More general recursive HITs are a separate extension.

## Circle's resolved metadata

For illustrative resolved IDs `C = InductiveId(0)`, `B = ConstructorId(0)`, and
`L = HigherConstructorId(0)`, use:

```text
family C:
  name = Circle, universe = 0
  parameters = [], indices = []
  constructors = Higher([Point(B), Higher(L)])

point B:
  inductive = C, name = base
  arguments = [], result_indices = [], recursive_arguments = []

term t_base = Term::Constructor(B)

higher L:
  inductive = C, name = loop
  arguments = []
  dimensions = ["i"]
  result_indices = []
  boundary.pieces = [
    { face: F::Eq(D::Bound(0), D::Zero), term: t_base },
    { face: F::Eq(D::Bound(0), D::One),  term: t_base },
  ]
```

The resulting interior family is reconstructed from the owner and its uniform
parameters: `Term::Inductive(C)`, here simply `Circle`. It is not stored as an
independently forgeable result-family term. The boundary terms have type Circle
under their respective faces, in the one-dimension context; they contain no
dimension occurrences. The higher record represents `loop(i) : Circle`, not a
point constructor returning `Path Circle base base`. A future path abstraction
over that interior exposes the surface constant `loop : base == base`.

## Trusted validation contract

Structural validation must precede all semantic lookup/evaluation. It checks
every reachable term ID as well as declaration IDs before indexing an arena.
Do not reuse the current restricted ordinary walker unchanged for a boundary
language with dimension binders.

| Invariant | Structural phase (A) | Semantic phase (B) |
| --- | --- | --- |
| Identity and ownership | Table position matches ID; owner exists; each tagged member exists, has that owner, and occurs exactly once; no orphan entries; kind and membership agree | No reliance on source names to repair a mismatch |
| Ordering | Boundary constructor references strictly precede this member and belong to its owner; reject cycles/forward references and unsupported reference kinds | Earlier point signatures are checked before use |
| Telescopes | Separate term/dimension arities and de Bruijn scope; at least one dimension for a higher record; no dimension payload on a point record | Parameter/index/argument domains are types; enforce the existing constructor-field universe bound and dependent telescope checking |
| Results | Exactly the owner's index count; result parameters implicit and uniform; no forbidden occurrences | Check each index in its dependent domain, instantiated with parameters and all previously checked result indices, at generic constructor dimensions |
| Boundary syntax | All pieces use scoped `F`/`D` and admissible terms; apply the nonrecursive whitelist even on impossible faces | Under each face, check its term against the reconstructed result family, including all parameters and indices |
| Coverage | Derive intended extent from dimensions; caller cannot assert an arbitrary coverage certificate | Prove extent equivalence with face entailment, as below |
| Coherence | Enumerate every pair within resource bounds | Typed conversion of the two terms under the intersection of their faces |

For `k > 0`, the intended boundary is the entire cubical perimeter:

```text
partial(k) = OR (i_l = 0 OR i_l = 1), for l = 1 ... k
coverage   = OR piece.face
```

Require `partial(k) entails coverage` and `coverage entails partial(k)` at
generic dimensions, under top. Equivalently each piece must lie in the
perimeter and their union must cover it. This permits subdivision by Cartesian
faces, including diagonals intersected with perimeter faces; it excludes an
unrestricted diagonal or `Top` as extra interior equations. There is no caller-
supplied extent to shrink to `Bot`. Arbitrary attaching subobjects are future
work. `partial(1)` is **not** top. Full boundary coverage is not interior
coverage, and neither check samples only endpoints.

Let `R(p,a,d) = D p rho(p,a,d)` be the reconstructed result family. For each
piece `(phi,b)`, check `b : R` under `phi`; family parameters remain the same
locals, and indices may specialize under `phi`. For every pair, check
`b_s = b_t : R` under `phi_s AND phi_t`. Inconsistent intersections discharge
conversion vacuously only after structural checks. Circle's intersection
implies `0 = 1`; in two dimensions, faces `i = 0` and `j = 0` intersect in a
consistent corner and must agree. An additional user-supplied path between
unequal pieces is not a substitute for this judgmental coherence requirement.

Dimension substitution maps binders to `0`, `1`, or ambient variables. Apply it
simultaneously and capture-avoidably to faces, result indices, boundary terms,
and their checking context. Semantic checking instantiates fresh dimension
levels in `Env.dims` and translates `F` into session-local `FaceId`s. Persistent
metadata stores `F`/`D`, never semantic levels or arena IDs. Endpoint
substitution, weakening, renaming, diagonals (`i := j`), and composition of
substitutions must preserve typing, coverage, and agreement. Identifying
dimensions can activate additional pieces; agreement makes this unambiguous.
Do not cancel delayed substitutions while keeping the old face context.

## Constructor terms and values (future Slice C)

`Term::Constructor(ConstructorId)` is sufficient for `base` and insufficient for
`loop`'s interior. Preserve its point-only meaning. Introduce a saturated form:

```text
Term::HigherApp {
  constructor: HigherConstructorId,
  parameters: Vec<TermId>,
  arguments: Vec<TermId>,
  dimensions: Vec<D>,
}
Val::HigherApp {
  constructor: HigherConstructorId,
  parameters: Vec<ValId>,
  arguments: Vec<ValId>,
  dimensions: Vec<Dim>,
}
```

There is no independent owner or result-index payload to forge: derive both
from checked metadata. Check exact arities, parameters and dependent arguments,
and dimension scope. Instantiate result indices from the supplied environments
to infer its type. Unsaturated term application uses ordinary lambda wrappers;
dimensions use path abstractions, never a term `Pi` over an invented interval
type. For Circle the name `loop` will elaborate to
`PLam(HigherApp(L, [], [], [D::Bound(0)]))`; `loop @ r` uses existing `PApp` beta
substitution to reach `HigherApp(L, [], [], [r])`. The path type is checked
against the boundary certificate, not asserted by the resolver.

Forcing a higher application instantiates its boundary, then checks which faces
are entailed by the ambient face. If a piece is active, return its instantiated
term; multiple active pieces agree by validation. A fixed order may select one
only after that agreement is established. If no individual piece is entailed
(including a disjunctive ambient context covered by several pieces), retain the
application; typed conversion may split the face context using existing face
reasoning. Do not invent an interior value by choosing a boundary piece.

Substitution, quotation, type recovery, conversion, hash/intern support, and
face-sensitive forcing all need explicit cases. Same-head congruence can compare
arguments/dimensions, but higher constructors are not globally disjoint or
injective: boundary reduction may equate distinct heads. Quotation must retain
generic dimension arguments and be recheckable. Cache keys must preserve face
context and substituted arguments. None of these changes are part of this task.

## Dependent elimination and coherence (future Slice D)

For `P : (x : Circle) -> U u`, the intended methods are exactly:

```text
base_case : P base
loop_case : Path i (P (loop @ i)) base_case base_case

circle_elim P base_case loop_case : (x : Circle) -> P x
```

Here `Path i A l r` is the **existing dependent core path**, written in the
S-expression core as `(Path i (app P (at loop i)) base_case base_case)`.
The family under its binder is `P(HigherApp(L, [], [], [Bound(0)]))`.
The endpoints are outside that binder and have types `P base`, by higher
boundary reduction. An introduction is `path i => m(i)` checked at this
dependent path type, with both restrictions equal to `base_case`. Writing only
`base_case == base_case` would incorrectly replace the varying family by the
constant `P base`. Current homogeneous surface syntax cannot state this general
dependent method type; kernel generation/checking can use `Term::Path` directly.
No new equality primitive or proof-irrelevant coherence field is proposed.

Choose a separate future `HitElim` term/value form with the current `Elim`
payload shape (owner, parameters, motive, ordered methods, indices, scrutinee),
but methods ordered by the tagged full constructor list. The checker derives
every expected method type; it never trusts a supplied method-type certificate.
For Circle it requires both methods even when the scrutinee is `base`. Reuse
ordinary point method generation only behind this HIT-aware checker. Ordinary
matching must not expose a supposedly exhaustive single `base` branch.

For a family `D p z`, use motive `P : (z : Indices p) -> D p z -> U u`.
After binding a constructor's arguments, its method is a section, at generic
dimensions `d`, of `P (rho(p,a,d)) (HigherApp(h,p,a,d))`. On each face its
restriction must be the elimination of that boundary term, at the restricted
indices. Earlier point boundaries compute using earlier point methods. The
initial nonrecursive fragment needs no induction hypotheses. A later recursive
extension must derive hypotheses at each recursive value's own indices and
define their action in boundary terms; ordinary recursive annotations alone
do not establish this action.

For one dimension this section is a dependent `Path` with endpoints generated
from the two boundary eliminations. For a full `k`-cube with canonical facet
terms it can be presented by iterated existing dependent paths in declared
binder order: abstract all but the first dimension on the first pair of facets,
then recursively form the inner path type. At every stage shared edges/corners
must convert. General subdivided face systems may not supply canonical total
facet terms. Their method is specified instead by the section judgment plus
all face restrictions; generating an existing iterated-path presentation needs
a checked facet-assembly procedure. Such declarations remain metadata-only
until that procedure and multi-dimensional elimination are justified. Circle
requires neither a new partial-element type nor that extension.

Universe checking must check `P` and both methods with ordinary cumulative
compatibility; do not equate universe levels. The intended Circle eliminator is
universe-polymorphic at the schema level for each explicit `u`. Slice D must
review and document this large-elimination policy explicitly; the ordinary
roadmap's unresolved general policy is not a proof for arbitrary HITs.

## Intended computation, separated by responsibility

| Rule | Intended equation | Reuse versus new work |
| --- | --- | --- |
| Point iota | `circle_elim P b l base --> b` | Reuse point-method application inside the new full-method checker/dispatch |
| Higher elimination | `circle_elim P b l (HigherApp(L,[],[],[r])) --> l @ r` | New HIT eliminator reduction; path application then uses existing machinery |
| Constructor boundary | `HigherApp(L,[],[],[0 or 1]) --> base`, also under entailed endpoint faces | New face-sensitive higher-value forcing; existing dimension substitution and entailment are ingredients |
| HIT composition | A checked composition retains its source and tube restrictions and commutes with higher boundary reduction | Requires a new justified rule; no fieldwise HIT rule specified here |

The critical diamond at an endpoint is explicit: higher elimination then path
endpoint reduction yields `b`; constructor boundary reduction then point iota
also yields `b`. For general pieces the corresponding diamond uses the checked
method restriction to elimination of that piece. Test these under substitution
and ambient faces, not only for closed endpoints. Path checking can validate a
generated method once higher endpoints compute; it cannot create the missing
higher-constructor or eliminator reductions itself.

## Composition obligations and alternatives (future Slice E)

Do not extend `compose_inductive` to higher heads, or call it for point heads
whose family has higher constructors. Before E, HIT compositions remain blocked
apart from the existing generic source-equals-target and entailed-tube rules.
This is an experimental intermediate calculus, not completed computational HIT
support or a canonicity claim.

The ordinary “same constructor + compose fields” rule ignores a higher
constructor's dimension arguments and attaching boundary. `loop(i)` has no term
fields, yet restricts to the different head `base` at either endpoint. On a tube
`i = 0`, a generic loop cap may consequently appear as a point. Conversely two
generic loop values can carry different dimension arguments; an empty field
list is no reason to identify them. The interval is not a type whose elements
can be composed as another ordinary field. Choosing an endpoint loses interior
data, and mixing fields with boundary reductions can break substitution even
if source/target values happen to agree.

Every proposed rule must establish at least:

1. The result has the target family, with dependent parameter/index lines and
   any argument filler telescope tracked generically, not just at endpoints.
2. Source/target equality and each tube restriction hold, including their
   overlaps with all instantiated constructor-boundary faces.
3. Restricting a composition to an attaching face agrees with composing the
   reduced boundary data; reducing a constructor before or after restriction
   cannot produce incompatible answers. Diagonal substitutions must preserve
   this property as well as endpoint substitutions.
4. Newly active boundary equations are reconsidered after substitution or face
   strengthening. Disjunctive covers require coherent face-local reasoning;
   cache entries cannot silently retain a generic interior head on a boundary.
5. Elimination of composition has a specified dependent action in the motive,
   respecting its method coherence. Eliminating only constructor heads and
   ignoring formal composition values is not a full computational eliminator.

Plausible strategies remain alternatives pending Cartesian justification:

- **Formal HIT composition values:** retain a checked `Com`-like canonical
  operation for HITs, with source/tube/boundary equations and dependent
  elimination into motive composition. This makes missing constructor shapes
  explicit but requires quotation, conversion, and a coherent eliminator action
  over these values; merely keeping today's neutral `Com` is not that proof.
- **Constructor-specific boundary-aware reduction:** reduce selected uniform
  boxes using actual argument fillers and boundary corrections, retaining
  formal/blocked composition otherwise. This can improve computation, but must
  prove compatibility of those corrections with all attaching faces and indices.
  No dimension filler using meet, join, or reversal is available by default.

E should first address the unparameterized Circle fragment and state its exact
rule and reduction scope. General argument/index-varying HIT composition is a
later extension unless independently justified. Retain the ordinary regressions
for generically varying parameter/index lines with equal endpoints. Add boxes
whose tube reduces `loop(i)` to `base`, mixed heads exposed by restrictions,
disjunctive covers, inconsistent faces, diagonal substitutions, and elimination
of formal compositions. Compare reduction orders and recheck quoted results.
Agreement of optimized/reference engines is regression evidence only: both
share the same mathematical reduction rules.

## Surface elaboration boundary

`Expr::Equality` can already represent `loop : base == base` in a parsed data
declaration. `data_declaration` currently demands that each constructor result
have the declared family as its application head, so it rejects this result.
Keep that behavior until semantic metadata validation and executable gates are
ready. Parsing is not acceptance by the kernel.

Future elaboration should classify a result returning `D p indices` as a point
candidate, and a path result with endpoints in that family as a higher candidate.
For homogeneous `left == right`, infer/check the endpoints' family, ensure it is
the declared owner with uniform parameters, introduce a fresh dimension, and
produce two resolved endpoint pieces. Bind ordinary arguments before that
dimension according to the metadata convention. Kernel checks must independently
revalidate ownership, indices, boundary types and coherence. Do not infer a HIT
merely because an ordinary constructor has a path-typed argument: its result
still determines its kind. Conversely, do not discard a path result to make a
point constructor returning the owner.

Resolve earlier constructors in declaration order; resolve `loop` uses through
the checked path wrapper described above. More general dependent path-result or
multi-dimensional surface declarations need explicit syntax and checking work;
do not pretend homogeneous `==` states every such family. Surface `match` on a
HIT remains rejected until a surface form can supply coherence methods. Slice F
may expose Circle declarations and path uses without claiming ordinary pattern
syntax can express dependent HIT elimination.

## Adversarial declarations and resource bounds

| Malformed candidate | Rejection point |
| --- | --- |
| Circle boundary `i = 0 -> true` | B: `Bool` is not Circle (A's initial boundary whitelist also rejects it) |
| One binder but `F::Eq(D::Bound(1), Zero)` | A: escaped dimension, regardless of whether the face would be inconsistent |
| Boundary `Other.base`, or a forged point ID with a different owner | A: wrong owner/reference; B independently checks the expected family |
| Two pieces on `i = 0` returning distinct point constructors | B: failure of typed conversion on the consistent overlap; in 2D also test disagreement between `i = 0` and `j = 0` |
| Missing `i = 1`, `Bot` coverage, or `Top` as a piece | B: failed perimeter coverage/equivalence; `Top` improperly constrains the interior |
| Missing result index | A: arity mismatch |
| An index of the wrong type, a later index ignoring dependency, or a boundary point at an unequal index | B: sequential dependent index checking or boundary family conversion |
| Out-of-range ID, owner ID altered, orphan, duplicate membership, or a Higher ID passed as a Point ID | A: checked lookup, ownership, uniqueness, and tag validation; C also checks every term reference against its typed table |
| Recursive field `x : D`, nested `List D`, negative field, or boundary using `Com`/self/higher/global alias | A: initial nonrecursive/term-grammar policy; there is no trusted annotation to override it |
| Higher record with zero dimensions, or point record smuggling boundary data | A: kind invariant / schema rejection |
| Surface point result relabeled as higher, or a path result relabeled as point | F: candidate classification plus A/B checks of the resulting signature; a fresh one-dimensional constructor with valid boundaries is legitimately higher even if its endpoints coincide |

Resolved metadata cannot recover an erased source signature: if an untrusted
elaborator emits a different but well-typed declaration, that is a source-
fidelity bug, not permission for the kernel to accept ill-typed terms. Test
classification round trips separately from the trusted structural invariants.
Likewise typed IDs alone do not authenticate raw numeric IDs constructed in
white-box tests: table/owner/membership checks remain mandatory.

Bound total constructors, binders, boundary pieces, term/face nodes visited, and
the quadratic pairwise-overlap workload. Use an explicit work stack or checked
depth limit for structural traversal, tracking scope in any memoization key.
Reject cycles in raw term/reference graphs before semantic recursion. Account
for all traversals and pair checks in one validation budget, so many small
pieces cannot evade a per-piece limit. Do not expand substitutions eagerly or
enumerate the `2^k` endpoints. The existing metadata depth guard (512), face
solver depth (256), expansion/clause limits, and evaluator fuel/node limits are
useful existing bounds, not a complete budget for this new pass. A must specify
concrete new aggregate limits and bounded-stack tests; B must propagate solver
and conversion exhaustion as inconclusive validation, never success. No
partial signature is published after an error. Do not retain semantic arena
IDs across checking sessions.

## Staged implementation plan and acceptance gates

All slices below are future work. This document implements none of them.

### HIT Slice A — structurally checked metadata only

Add generic higher IDs/records, tagged family membership, staging API states,
the dimension-aware scope walker, reference/kind checks, nonrecursive whitelist,
and explicit traversal budgets. Build Circle metadata directly in Rust tests;
exercise malformed IDs, dimensions, ordering, duplicate membership, kind errors,
and resource limits. Keep structural candidates out of executable programs.
No term/value extension, evaluator rule, or surface acceptance.

### HIT Slice B — semantic validation

Check telescope sorts/universes, generic result indices, each boundary's full
family type, perimeter coverage and all overlaps. Use fresh generic dimensions
and the existing Cartesian face solver. Initial boundaries refer only to earlier
point constructors, so B does not require C's evaluator. Add wrong-type/index,
missing/extra coverage, coherent/incoherent 2D-corner, and substitution tests.
Issue an immutable semantic signature certificate, still gated from execution.
This certificate does not certify future multi-dimensional elimination or Kan
rules. No surface HIT acceptance.

### HIT Slice C — higher applications and boundary reduction

Introduce saturated `HigherApp` terms/values, checked path wrappers, scoped
substitution, forcing, quotation and conversion. Gate executable signatures to
the supported one-dimensional nonrecursive fragment. Route Higher families away
from ordinary `Elim`, pattern matching, and `compose_inductive` before enabling
any such terms. Test generic `loop @ i`, both endpoints, face restrictions,
disjunctive contexts, capture avoidance, conversion after forcing/substitution,
and normalize/recheck in both modes. No new HIT composition or eliminator yet.

### HIT Slice D — dependent eliminator coherence

Add `HitElim`, full tagged method ordering, and generated Circle method type
`Path i (P (loop @ i)) base_case base_case`. Document the explicit universe
policy. Implement point iota and higher-method application; reject missing or
wrong endpoint methods. Test a genuinely dependent motive and both paths around
the endpoint computation diamond. Compositions may remain blocked at this
intermediate stage; do not call this a complete computational HIT calculus.

### HIT Slice E — Cartesian composition integration

Select and justify a precise strategy from the alternatives above, starting with
Circle. Specify its boundary/substitution laws and dependent elimination on
composition values before implementation. Add adversarial boundary boxes and
reduction-order tests, preserve existing ordinary blocking rules, and record
remaining metatheoretic gaps. Do not enable more general metadata fragments by
accident when only Circle's composition fragment has been reviewed.

### HIT Slice F — surface `data Circle`

Only after A–E, classify point/path results, emit checked boundary metadata, and
resolve higher names through path wrappers. Accept the target declaration and
test endpoint computation through the public library. Add rejection tests for
wrong owners, path-result misclassification, and unsupported dependent/multi-
dimensional declarations. Keep HIT `match` rejected unless coherence syntax is
also provided. Update README implementation claims only for the fragment that
actually passes this gate.

For each slice that changes Rust, require `cargo fmt --all -- --check`,
`cargo clippy --all-targets --all-features -- -D warnings`, and
`cargo test --all-targets --all-features --locked`. The present documentation-only
change adds no tests and changes no runtime behavior; it does not mark HITs as
implemented or supersede the existing ordinary-inductive trust boundary.
