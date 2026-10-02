# Higher inductive types: trusted representation and Circle plan

Status: **Slices A/B/C implemented**, with an internal one-dimensional,
nonrecursive higher-application and boundary-reduction fragment. HIT elimination,
HIT composition, mixed Ordinary/Higher signature imports, and surface HIT
declarations remain unimplemented. Ordinary inductives and homogeneous surface
paths are implemented; they do not already provide higher constructors. The
new core fragment changes no mathematical behavior of existing ordinary programs.

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
single ordered, tagged membership list on a HIT family. The following is the
integrated schema used by C; A/B still validate separate staging tables:

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

### Implemented Slice A staging gate

`src/hit.rs` defines `RawHigherMetadata` with its own term arena, point table
(reusing `ConstructorDecl`), higher table, and `HigherFamilyDecl` table. Each
staged family has one ordered `Vec<ConstructorRef>`; higher IDs have a distinct
Rust type from point IDs. All IDs resolve locally within these staging tables.
A/B do not publish an executable program. The crate-private C gate
`SemanticallyCheckedHigherMetadata::publish` explicitly checks the executable
capability and copies metadata into a tagged program. Slice B's separate
point-signature view is still validation-only and never escapes.

`RawHigherMetadata::validate(&self)` returns a
`StructurallyCheckedHigherMetadata<'_>` only after the entire structural pass
succeeds. The certificate's private field holds an immutable borrow of the raw
arena and all its tables; Rust prevents mutation for the certificate's lifetime.
Accessors expose only shared data. Only the structural certificate is accepted
by B; only the semantic certificate offers C's explicit one-dimensional
publication gate. No certificate itself is executable. A published raw core
program is revalidated before becoming an immutable `CheckedProgram`.

The consumer audit covered `validate_inductives`, semantic declaration checking,
generic eliminator checking and method generation, evaluator iota and
`compose_inductive`, constructor conversion/type recovery, quotation of heads
and eliminator methods, and surface constructor resolution, matching and
exhaustiveness. A/B left those consumers unchanged. C now migrates
`InductiveDecl.constructors` to `FamilyConstructors` and requires an explicit
`ordinary()` check at ordinary-only consumers. There is no authoritative
point-only list alongside a Higher family's tagged membership.

The structural grammar is exactly the ordinary metadata term whitelist:
`Var`, `Pi`, `Sigma`, `App`, `Ann`, `Path`, `Suc`, universes, primitive Bool/Nat
forms, `Inductive`, and point `Constructor` references. Current-family heads and
constructor constants are excluded except for the outer boundary point head.
All referenced IDs are range/identity checked. Other staged-family references
must refer to an earlier family table entry; this conservative staging policy
rules out mutual declaration dependencies without unfolding. Globals remain
forbidden. `PLam`, `PApp`, `Com`, eliminators and other executable forms remain
outside the whitelist even inside a field. In particular constructor arguments
cannot smuggle in constructor dimensions through path application. `Path`
increments only the dimension scope of its family, while `Pi`/`Sigma` increment
only the codomain's term scope. Endpoints inherit the outer scopes.

The raw arena is append-only, but a forged predicted `TermId` can still create
a self/forward edge or cycle. Iterative term traversal uses an active-path set
to reject cycles, while permitting shared DAGs. Application-spine traversal has
its own cycle check; the depth budget includes both spine and field traversal.
Boundary references can only name an earlier point of the same owner. There is
no term form carrying a higher ID, so self/higher boundary applications cannot
be expressed in this slice. Numeric reinterpretation as a point ID refers to
that point table entry or fails lookup; it never creates a higher application.

Concrete limits for one validation call are:

| Resource | Limit |
| --- | --- |
| Staged families | 128 |
| Point and higher constructors combined | 4,096 |
| Dimensions per higher constructor | 16, with at least one required |
| Entries per parameter/index/argument telescope | 256 |
| Boundary pieces per higher constructor / total | 256 / 4,096 |
| Term node visits / face node visits | 100,000 / 32,768 |
| Traversal depth, root at zero | 128 |
| Aggregate validation work | 200,000 |

Work is charged for table/membership/binder/index/piece traversal, dimensions,
term enter/exit events, face nodes and boundary application traversal. Repeated
visits to shared terms count again; no scope-insensitive memoization can hide
work or scope errors. Individual limits and the aggregate work cap both apply,
so the latter may be reached first. Validation uses explicit work stacks rather
than recursive traversal, including for faces; exhaustion returns an error and
no certificate. These bound validation work on reachable metadata, not memory
already allocated by the raw-input producer. Tests include a 256 KiB worker
stack, over-depth terms/faces, shared-graph work exhaustion and exact limit
edges. No endpoint enumeration or face solver is used.

Scope checks run even on `Bot` faces. Conversely, empty/incomplete boundaries,
`Top` pieces that constrain the interior, and well-scoped but ill-typed result
indices can pass A: sort/index/boundary typing, perimeter coverage and overlap
conversion belong to B. The Circle fixture stores exactly the endpoint pieces
below, but source `data Circle` is still rejected by the ordinary elaborator.

### Implemented Slice B semantic gate

`StructurallyCheckedHigherMetadata::validate_semantic(&self)` issues
`SemanticallyCheckedHigherMetadata<'_>` only on complete success. Its private
field borrows the original immutable raw metadata. It retains no values,
environments, face IDs, generic dimension levels, or validation-only program.
There is no raw-to-semantic shortcut or unchecked certificate constructor.

The bridge in `src/hit_semantic.rs` is a child module of `check`, so existing
private context/sort/type operations need no wider visibility. It creates one
local `Program` containing family and point signatures and no declarations.
Family/point IDs keep their exact table positions; higher IDs are never inserted
into the point table. Reachable A-validated terms retain their exact arena IDs.
Unused syntax slots become inert placeholders: unvalidated unreachable terms
and deeply nested faces are never cloned or evaluated. Names are unnecessary
for validation and are not copied.

This incomplete point-only view never escapes the function, never becomes a
`CheckedProgram`, and is never stored in either certificate. A's unchanged
whitelist excludes elimination, composition and globals from all reachable
syntax. Therefore no user-visible exhaustiveness/elimination/composition claim
can use the missing higher members. B itself changes none of the executable rules. C's separately documented
integration changes the representation and adds runtime dispatch gates.

The bridge first reuses `check_inductive_declarations` for family telescopes and
point argument sorts/universes/dependent result indices. Higher argument sorts
use the same checker and field-universe bound. Parameters and arguments are
bound before fresh generic dimensions. Dimension environments append binders
in declaration order, so `Bound(0)` denotes the last dimension independently of
term locals.

Each higher result index is checked sequentially against its family's index
domain instantiated with parameters and previously checked index values.
The expected boundary type is reconstructed as the owner applied to those
parameter/index values. Each piece is checked against that type under its face.
The perimeter is a linear OR of the `2k` endpoint faces, and coverage is the OR
of declared faces. Both entailments use the existing Cartesian solver; there
is no endpoint sampling or Boolean interval assumption. Every unordered pair
uses typed conversion under the face intersection. Inconsistent intersections
are discharged by existing kernel logic only after A has checked the syntax.

One fresh engine serves the entire validation session. Limits never reset per
constructor, and a final engine budget check precedes success:

| Semantic resource, per full pass | Limit |
| --- | --- |
| Syntax arena slots, including unused positions | 100,000 |
| Higher constructors / boundary pieces | 4,096 / 4,096 |
| Coverage entailment calls | 8,192 |
| Aggregate unordered overlap pairs | 16,384 |
| Bridge work units | 200,000 |
| Aggregate evaluator/checker/conversion fuel | 1,000,000 |
| Aggregate semantic arena nodes | 250,000 |

Bridge work covers syntax reachability/copying, signature entries, higher
constructors, parameters/arguments/indices/dimensions, pieces, entailments and
overlap pairs. A's face-node/depth bounds and the solver's existing
depth/expansion/clause/cache limits also remain in force. Pair counts are
preflighted for the entire input before semantic checking. All solver,
conversion, fuel, node and bridge-budget errors propagate without certification.
The node cap uses the existing engine allocation-check convention, with checks
at operation boundaries and before return; it is not an exact byte-memory cap.

B alone gives Circle a semantic certificate; C publication is a separate step. Tests cover
independent sessions; dependent parameter/argument/index telescopes; point and
higher sort/universe failures; incorrect result/boundary indices; coherent and
incoherent complete 2D perimeters; disjunctive/clipped-diagonal coverage;
dimension order; sparse/unreachable syntax; aggregate pairs; and solver/fuel/
node/work exhaustion. Empty, one-sided, `Bot`, `Top`, unrestricted diagonal and
ill-typed fixtures continue to pass A and fail B for their semantic defect.
Surface Circle remains rejected after certification. B certification does not itself
authorize execution, elimination or composition. C requires an additional gate.

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
| Coverage | Store dimensions and scoped faces, without a caller-supplied coverage certificate | Derive the intended extent and prove extent equivalence with face entailment, as below |
| Coherence | Bound piece counts; no overlap traversal in A | Enumerate every pair within work bounds and check typed conversion under the intersection of their faces |

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

## Constructor terms and values (Slice C implemented)

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
context and substituted arguments. These cases are implemented in C; higher elimination and Kan rules remain future work.

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
useful existing bounds, not a complete budget for this new pass. The implemented
A limits and bounded-stack tests are listed above; B must propagate solver
and conversion exhaustion as inconclusive validation, never success. No
partial signature is published after an error. Do not retain semantic arena
IDs across checking sessions.

## Staged implementation plan and acceptance gates

Slices A/B retain staging validation. C adds a gated internal executable fragment.
Slices D–F remain future work.

### HIT Slice A — structurally checked metadata only

Implemented in `src/hit.rs`: generic higher IDs/records, tagged family membership,
raw/checked staging API states, a dimension-aware scope walker, reference/kind
checks, the nonrecursive whitelist, and explicit traversal budgets. Rust tests
construct Circle directly and exercise malformed IDs, dimensions, ordering,
duplicate membership, kind errors and resource limits. Structural candidates
remain outside executable programs. A itself performs no semantic checking;
B below adds that separate gate. Neither adds term/value extensions, evaluator
rules, or surface acceptance.

### HIT Slice B — semantic validation

Implemented by the semantic certificate in `src/hit.rs` and the private kernel
bridge in `src/hit_semantic.rs`, as detailed above. Telescope sorts/universes,
dependent indices, boundary typing, exact perimeter coverage, and typed overlap
coherence are checked within aggregate budgets. Initial boundaries still refer
only to earlier point constructors, so B requires none of C's evaluator rules.
The immutable certificate remains gated from execution and certifies neither
future multi-dimensional elimination nor Kan rules. No surface HIT acceptance.

### HIT Slice C — higher applications and boundary reduction

Implemented: saturated `HigherApp` terms/values, checked core path wrappers,
capture-avoiding substitution, boundary forcing, quotation/type recovery and
conversion. The executable gate accepts one-dimensional nonrecursive signatures
only. Higher families cannot enter ordinary elimination, surface point
resolution/matching, or ordinary constructor-directed composition.

C uses `SemanticallyCheckedHigherMetadata::publish` to copy validated metadata,
preserving family, point, higher and term IDs. It does not expose B's temporary
view. `Program::validate_inductives` dispatches tagged Higher programs through
A/B again, so internal forged programs cannot bypass semantic validation or the
dimension limit. Publication currently produces all-Higher signatures; combining
ordinary family imports with them is deliberately rejected rather than
misclassifying a family. Standalone ordinary programs retain their existing
validation/recursion support. Core runtime arguments can use the existing
primitive Nat/Bool and function/pair/path forms.

An iterative, cycle-aware executable-term preflight validates declaration IDs,
term/dimension scopes (including impossible faces), arities and global ordering
before checking. It uses A's 100,000 term visits, 32,768 face visits, depth 128 and
200,000 work units, plus a 100,000-slot executable arena cap. Runtime evaluation,
conversion and normalization retain the existing fuel/node limits.

Forcing instantiates the boundary environment from parameters, arguments and
dimensions and reduces only when the ambient face entails an individual piece.
Otherwise the generic higher head remains. Typed conversion splits disjunctive
faces and uses dependent same-head argument congruence after boundary forcing;
there is no higher-head injectivity or disjointness rule. Substitution traverses
both term and dimension payloads, including delayed/composed substitutions, and
the existing face-sensitive cache keys are preserved.

Ordinary composition returns blocked `Com` on Higher families, including a
point cap. Existing universal source=target and active-tube equations still
apply; no higher Kan/composition rule is claimed. Ordinary `Elim` is rejected
by checking, method/motive construction, evaluation and quotation, even on base.

Text quotation retains generic higher payloads using diagnostic
`(higher name (terms...) (dimensions...))` output; this is not new parser syntax.
The internal `quote_core` path produces scoped core syntax for normalize/recheck
without parsing that diagnostic text. Its limits are depth 32, 100,000 output
term nodes, and 32,768 aggregate face nodes with face depth 128. It supports the
all-Higher C fragment; structured ordinary-eliminator quotation is outside this
new API. Existing ordinary text quotation is unchanged.

Regressions cover both evaluation modes, Circle endpoints/interior, shared
face caches, covers/diagonals, distinct higher heads agreeing on their boundary,
dependent parameters/fields/indices, nested dimensions, structured quotation
rechecking, malformed/cyclic raw terms, impossible-face scope errors, forged
signatures, two-dimensional publication rejection and runtime resource errors.
Surface Circle and surface ordinary matching on Higher families remain rejected.
Run `cargo test hit::runtime --locked` for the focused C tests.

No HIT eliminator, HIT composition, parser extension, or surface HIT declaration
is included. This intermediate core is not a complete computational HIT calculus.

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
`cargo test --all-targets --all-features --locked`. Slice A also has the focused
command `cargo test hit::tests --locked`, now including semantic fixtures.
B's bridge/budget tests use `cargo test check::hit_semantic --locked`.
Structurally or semantically checked staging metadata
does not constitute executable HIT support or supersede the existing
ordinary-inductive trust boundary.
