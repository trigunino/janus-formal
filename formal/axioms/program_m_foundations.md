# Program M — Foundational relational pilot

## Status

This file fixes the first **pilot language**, not the ontology of the physical
Universe. Competing foundational languages remain admissible.

## Primitive signature

`MF-A0` supplies only:

- a type `Obj` of primitive objects;
- a type `Rel` of primitive relation labels;
- a truth-valued incidence predicate `holds : Rel -> Obj -> Obj -> Prop`;
- relabellings of objects and relations that preserve `holds`.

No finiteness, topology, order, metric, dimension, differentiability,
probability, causal direction, field, sector exchange, PT symmetry, action or
gorge is included in `MF-A0`.

Probability enters only in the separate `MF-ENS-001` ensemble branch. Its
exchangeability and projectivity assumptions are declared additions, not
consequences of `MF-A0`.

The use of binary relations is a pilot restriction. Higher-arity, enriched,
categorical, algebraic and spectral primitives must be recorded as distinct
branches rather than encoded silently.

## Coefficient language

The primitive relational signature remains value-free. When scalar values are
needed, the ambient coefficient language may be a signed additive group such
as `ℝ`. This single language includes zero, nonnegative restrictions and signed
assignments; an "unsigned base" is therefore not maintained as a competing
ontology.

Allowing negative values does not impose a Janus sector structure. A chosen
nontrivial involution, odd equivariance `q(σx) = -q(x)`, nonvanishing and a
physical interpretation remain explicit additional hypotheses.

## Equivalence

Two `MF-A0` systems are equivalent only when bijections of `Obj` and `Rel`
preserve and reflect `holds`. Weaker observational equivalences belong to later
stages and must not be confused with foundational isomorphism.

## Reconstruction ladder

Each arrow is an open theorem or construction:

```text
MF-A0 relational system
  -> MF-R1 derived reachability or neighbourhood
  -> MF-R2 candidate topology
  -> MF-R3 candidate dimension/continuum structure
  -> MF-R4 candidate metric or causal structure
  -> MF-R5 fields, symmetries and sectors
  -> MF-R6 geometry candidate
  -> Program P adapter
```

No later structure may be used to define an earlier arrow unless the result is
explicitly labelled circular or conditional.

## Anti-smuggling tests

Every reconstruction claim must provide:

1. the exact axioms used;
2. invariance under `MF-A0` equivalence;
3. a proof that the output is well-defined;
4. a uniqueness statement or explicit multiplicity;
5. a countermodel showing which dropped hypothesis breaks the conclusion;
6. a classification as necessary, conditional, possible or impossible;
7. a check that Janus-specific structure was not encoded in definitions.

In particular, a two-colouring is not evidence for two physical sectors, a
cycle is not a throat, an involution is not PT, and graph distance is not a
physical metric without additional reconstruction theorems.

## First theorem targets

- `MF-TOP-001` (**T**): every selected binary relation yields an Alexandrov
  upper-set topology after the explicitly declared reflexive-transitive
  closure;
- `MF-TOP-002` (**T**): foundational isomorphisms induce homeomorphisms of the
  reconstructed spaces.
- `MF-CONF-001` (**T/X**): relational systems and their exact simultaneous
  object/relation relabellings form a groupoid; identity, composition,
  associativity and inverses are proved in Lean, with an independent finite
  automorphism audit.
- `MF-OBS-001` (**T/X**): scalar assignments are admissible on the
  configuration groupoid exactly when they are constant along relational
  isomorphisms; labelled probes are rejected by an exhaustive two-object audit.
- `MF-COMP-002` (**T/X/N**): configurations with a common relation signature
  have a canonical disjoint composition, associative and commutative up to
  isomorphism with an empty unit; cross-component relations require additional
  interface data and are not determined by the pieces.
- `MF-GLUE-001` (**T/X/C**): a compatible induced relational interface and two
  embeddings define a free pushout gluing that retains exactly the relations
  witnessed in either piece; incompatible interfaces are rejected and the
  interface remains explicit input.
- `MF-GLUE-002` (**X/C/N**): a finite multi-interface diagram has an
  order-independent free gluing under all six interface orders in the audit and
  is invariant up to relabelling; local pieces still do not determine arbitrary
  nonlocal relations, so unrestricted global uniqueness is refuted.
- `MF-DESC-001` (**T/X/N**): primitive descent identifies the unique minimal
  global relation witnessed by local patches, while reflexive-transitive
  reachability is reconstructed only after gluing and may legitimately cross
  several patches.
- `MF-DESC-002` (**T/X**): under primitive descent, global reachability is
  equivalent to a reflexive-transitive chain of locally witnessed primitive
  steps; 4,096 random diagrams confirm that global closure matches direct chain
  exploration, while patchwise closure followed by union fails.
- `MF-FREE-001` (**T/X**): reachability is the least preorder containing the
  primitive relation; its universal mapping property is proved in Lean and an
  exhaustive rank-three audit checks all 512 relations against all 29
  preorders. No order, topology or geometry is inferred beyond this closure.
- `MF-GEO-001` (**X/N**): the free preorder generated by one primitive arrow
  on four objects feeds the MF-MAN-008 rank reconstruction and yields six
  realizations in two inequivalent metric classes. Primitive relations alone
  therefore do not select a unique metric geometry.
- `MF-GEO-002` (**X/N**): two overlapping patches and their common interface
  each have a unique rank-metric class, while their global union has two. Local
  uniqueness and interface agreement therefore do not select global geometry.
- `MF-REF-001` (**T/X/N**): joint visibility of every ordered pair is necessary
  and sufficient for restrictions to determine arbitrary pair-valued global
  data uniquely. This repairs MF-GEO-002's missing pair but supplies neither
  existence nor selection of local metric values.
- `MF-DIST-001` (**X/C**): assigning unit cost to primitive arrows canonically
  generates their extended directed shortest-path distance. All 65,536 rank-four
  relations pass triangle and relabelling audits, but the result is a Lawvere
  geometry and does not select a Lorentzian metric.
- `MF-WEIGHT-001` (**X/N**): on the rigid directed three-chain, all nine
  positive integer weightings in `{1,2,3}²` are invariant and glue-compatible;
  fixing the first edge to unit cost still leaves three relative weights. The
  declared relational principles cannot select primitive weights.
- `MF-MEAS-001` (**T/X/N**): additive atom weights remain arbitrary under the
  automorphisms of a rigid relation. Full permutation-uniformity instead forces
  finite mass to equal cardinality times one atom mass, proved in Lean; this is
  an added uniformity axiom and interval counting remains insufficient by
  MF-MAN-009.
- `MF-SIGN-001` (**T/X/C**): an explicit involution and odd transformation law
  pair charges as `q(σx)=-q(x)`, forcing zero pair total and zero charge at fixed
  points. Ordinary invariance plus oddness forces the zero charge, while the
  magnitude of a nonzero odd pair remains free.
- `MF-INV-001` (**X/N**): naturality forces any intrinsically selected
  involution into the centre of the relation's automorphism group. The empty
  three-object relation has three nontrivial involutions but only the identity
  is central, refuting a universal nontrivial canonical selector.
- `MF-INV-002` (**X/N/C**): unique nontrivial central involutions are not closed
  under disjoint composition across all eligible rank-two relations. If the
  involutions are retained as explicit structure, their componentwise sum is
  always a valid relational involution in the audited composites, though not
  necessarily central after forgetting the chosen structure.
- `MF-INV-003` (**T/X/C**): a chosen componentwise involution descends through
  an interface quotient exactly when it preserves the generated equivalence
  relation. Lean proves involutivity on every such quotient; the finite audit
  accepts paired interfaces and rejects unpaired identifications.
- `MF-PBRIDGE-002` (**T/X/C**): every nonzero odd real M charge factors exactly
  into P's binary `JanusCharge` sign and a positive magnitude, and M's exchange
  maps to P's `ptCharge`. The adapter supplies no metric, throat, physical mass
  interpretation, mediator law or action.
  reconstructed spaces;
- `MF-NOGO-001` (**T**): non-isomorphic empty-edge and self-loop systems on
  two objects produce the same reconstructed topology;
- `MF-NOGO-002` (**T**): one directed two-object system has distinct upper-set
  and lower-set Alexandrov topologies;
- `MF-SEL-001` (**T**): upper-set and lower-set reconstruction coincide if
  and only if generated reachability is symmetric;
- `MF-ENUM-001` (**X**): exhaustively enumerate directed binary relations on
  one to four objects after quotienting simultaneous object relabellings.
- `MF-CAUS-000` (**T**): quotient mutual reachability using Mathlib
  antisymmetrization; the result is a partial order whose strict comparisons
  are exactly irreversible reachability.
- `MF-DEC-001` (**T**): decompose primitive objects into skeleton fibers and
  split the original relation uniquely into internal and bridge edges without
  information loss.
- `MF-COMP-001` (**X/N**): on one to four objects, audit successive invariant
  compressions and reject component-size/edge-count summaries as lossless
  decorations.
- `MF-OBS-000` (**T**): characterize safe compression for an observable by
  factorization, supply collision no-go witnesses and specialize the criterion
  to the bare and lossless skeleton representations.
- `MF-CAUS-001` (**T/N**): import local finiteness as the standard causal-set
  kinematics gate and prove that it is automatic, hence non-discriminating, on
  every finite Program M candidate.
- `MF-DIM-000` (**X/N**): compute exact finite-order invariants before any
  dimension interpretation and exhibit orientation-reversed orders sharing
  ordering fraction, height, width and interval-size profile.
- `MF-DIM-001` (**X/N**): invert the Myrheim–Meyer ordering fraction using only
  an order matrix, validate on held-out 1+1 sprinklings, and retain an
  anisotropic grid with a near-2 estimate as a non-sufficiency witness.
- `MF-LOC-001` (**X/N**): build a relabelling-invariant interval-abundance
  profile from order alone, freeze an L1 threshold on disjoint training seeds,
  accept held-out Poisson orders and reject the anisotropic grid.
- `MF-LOC-002` (**X/N**): repeat the frozen-rule protocol at four sizes and add
  valid KR-type three-layer controls. Both adversary families are rejected,
  but the preregistered Poisson gate fails at `N=256` and is retained.
- `MF-LOC-003` (**X/C**): on entirely fresh seeds, split each scale into
  reference, calibration and validation samples; use the finite conformal rank
  36/40 for 90% marginal coverage and retain both adversary families.
- `MF-GATE-001` (**X/I**): accept an order matrix only, validate the partial
  order laws, assemble frozen dimension/locality diagnostics with hashes and
  explicit unsupported/not-tested states, and never promote compatibility to
  geometry or physical causality.
- `MF-GATE-002` (**X/N**): accept an arbitrary primitive relation, form its
  reachability preorder and mutual-reachability quotient, report every measured
  loss, then run `MF-GATE-001`; distinct primitive relations are exhibited with
  identical quotient diagnostics.
- `MF-MAN-000` (**T/N**): prove that every partial order embeds exactly into a
  powerset by principal pasts, so unconstrained order embeddability is vacuous
  as a manifold-likeness test.
- `MF-MAN-001` (**I/T**): define a checked faithful-embedding contract with
  exact order reflection, conditional number-volume control, admissible scales
  and explicit sampling obligations; no geometric realization is claimed.
- `MF-MAN-002` (**T/N**): prove that `MF-MAN-001` is automatic for every finite
  partial order when target and volume are freely chosen; independent target
  geometry and volume are therefore necessary.
- `MF-MAN-003` (**I/T**): fix a target-owned causal order, volume and proper-time
  proxy, then require number-volume and intrinsic maximal-chain-step/proper-time
  laws. The intrinsic number of chain steps is invariant under order isomorphism.
- `MF-MAN-004` (**I/T**): instantiate the target interface with external 1+1
  Minkowski null coordinates and prove its order, volume and proper-time
  consistency. This is a test target, not an emergent geometry.
- `MF-MAN-005` (**X/N**): exhaustively test finite order compatibility with the
  1+1 product-order target through pairs of linear extensions; check fixed
  finite volume/time tolerances on a three-chain and retain the non-embeddable
  standard example `S₃`.
- `MF-MAN-006` (**X/N**): compare growing diagonal-chain and square-grid
  families at fixed density. The chain fails number-volume scaling; the grid's
  full-square discrepancy vanishes but a directional chain-time error persists.
- `MF-MAN-007` (**X/C**): execute a preregistered homogeneous-Poisson audit in
  the external 1+1 target at three densities, with fixed seeds, equal-volume
  directional regions and unchanged statistical thresholds.
- `MF-MAN-008` (**X/N**): enumerate every null-rank realization of every
  partial-order class through four objects and quotient metric signatures by
  order automorphisms; retain the first exact non-uniqueness witness.
- `MF-MAN-009` (**X/N**): calibrate density on maximal-cardinality intervals
  and score number-volume residuals only on the remaining intervals for every
  partial-order class through five objects; retain both selected and unresolved
  ambiguity witnesses.
- `MF-MAN-010` (**X/N**): calibrate the intrinsic longest-chain clock on
  maximal-step intervals and validate on shorter ones; combine its residual
  with number-volume only by weight-free Pareto dominance and retain the exact
  finite conflict.
- `MF-MAN-011` (**T/N**): prove the exact weighted-loss threshold for the first
  MF-MAN-010 conflict and prove that a change of diagnostic units reverses a
  fixed-weight choice; scalarisation is therefore an additional convention.
- `MF-MAN-012` (**X/T/N**): combine independently calibrated density and chain
  scale through the dimensionless external 1+1 identity `2 rho a²=1`; prove
  the first conflict ties exactly and exhaustively retain the failure to select
  through five objects.
- `MF-MAN-013` (**X/C/N**): calibrate finite Poisson fluctuations of the
  dimensionless identity at four densities with disjoint estimation regions
  and split-conformal rank 180/200; retain the exact square-grid collision.
- `MF-MAN-014` (**X/C**): calibrate the count variance-to-mean ratio across
  sixteen equal-volume target cells with a two-sided conformal interval; reject
  the square-grid collision and diagonal controls at all four fixed densities.
- `MF-MAN-015` (**X/C**): replace coordinate cells by the order-only immediate
  cover relation, average in/out link-degree dispersion to remove orientation,
  and conformally reject square grids and chains at four cardinalities.
- `MF-ADV-001` (**X/N**): generate 400 fresh coordinate-free forward-DAG and
  three-layer adversaries at `N=256`; retain 115 collisions with MF-MAN-015 and
  the absence of a collision with the frozen DIM/LOC/link intersection.
- `MF-ADV-002` (**X/N**): replace one element by an engineered antichain of
  exact past/future twins, validate six multiplicities on 240 fresh candidates,
  and retain 101 collisions with all three frozen order-only gates.
- `MF-MAN-016` (**X/C/N**): calibrate the largest exact past/future-twin class
  on fresh Poisson references with one-sided conformal rank 180/200; keep
  natural pairs and reject exact clone multiplicities at least four at `N=256`.
- `MF-ADV-003` (**X/N**): replace one element by repeated private two-level
  branches and retain 111 fresh collisions with DIM/LOC/link/exact-twin gates,
  including an eight-branch witness.
- `MF-MAN-017` (**X/C/N**): apply orientation-symmetric one-dimensional
  Weisfeiler–Leman refinement to full past/future multisets, calibrate stable
  color multiplicity on Poisson, and reject registered symmetric repetitions.
- `MF-ADV-004` (**X/N**): individualize a short generated fan with chains of
  lengths `1..m`; retain 126 fresh collisions with all five gates, including a
  passing 28-object fan.
- `MF-ID-001` (**T/N**): prove that one finite observation cannot universally
  identify its generator when two distinct laws have overlapping support.
- `MF-ENS-001` (**I/T**): define exchangeable, projectively consistent laws on
  finite posets and the held-out asymptotic separation certificate now required
  for an emergence claim. No concrete realization is claimed yet.
- `MF-ENS-002` (**X/T/N**): instantiate the first target/competitor pair with
  matched limiting pair density; retain the failed pilot threshold, separate
  them on fresh sizes using strict three-chain density, and prove exactly that
  the two-level competitor has no strict three-chain.
- `MF-ADV-005` (**X/T/N**): mix total, two-level and antichain laws to match
  exactly the Minkowski pair and three-chain means. The frozen gate rejects
  every fresh sample, but Lean proves that the two-moment signature is not
  injective. Whether to require ergodicity remains an explicit open choice.
- `MF-ADV-006` (**X/T/N**): use an iid six-level kernel satisfying the same two
  limiting moments inside each realization. It breaks the frozen gate on
  255/256 fresh samples, while Lean proves that its strict height is at most six.
- `MF-MAN-018` (**X/T/C/N**): require order-only longest-chain growth across
  fresh sizes and intersect it with the frozen pair/triple gate. It accepts all
  64 Minkowski trajectories and rejects the six-level, total and antichain
  controls; growth alone is explicitly insufficient.
- `MF-ADV-007` (**X/T/N**): replace six levels by a countable iid level law with
  a Zipf-2 tail. It matches both moments and square-root height growth, breaking
  the combined gate on 54/64 fresh trajectories. Its macroscopic twin classes
  identify the previously registered MF-MAN-016 diagnostic as the successor.
- `MF-MAN-019` (**X/T/C/N**): lift exact twins to an ensemble-scale fraction
  decay test. It accepts all 64 Minkowski trajectories and rejects MF-ADV-007,
  total-order and antichain controls in the frozen combined gate. Lean proves
  that a positive macroscopic lower bound prevents vanishing twin fraction.
- `MF-ADV-008` (**X/T/N**): decorate every infinite level by an independent
  random height-two bipartite order, retune the exact pair/triple moments, and
  retain square-root height while removing macroscopic exact twins. It breaks
  the frozen four-gate intersection on 58/64 fresh trajectories.
- `MF-PAT-001` (**X/T/C/N**): replace the open-ended scalar-gate sequence by the
  full distribution of induced finite subposets. At rank four the exact
  24-permutation Minkowski reference contains all 16 unlabelled posets, accepts
  60/64 fresh target batches and rejects all 64 MF-ADV-008 batches. Only the
  all-rank hierarchy, modulo kernel equivalence, is identifying.

The two positive results compile in
`JanusFormal.Foundations.ProgramMTop001`. They reuse Mathlib's
`Relation.ReflTransGen`, `Topology.upperSet` and `AlexandrovDiscrete`; these
library primitives were audited before adding project definitions. The finite
no-go witnesses compile in `JanusFormal.Foundations.ProgramMTopNoGo`.
The exact orientation-independence criterion compiles in
`JanusFormal.Foundations.ProgramMTopologySelection`. Uniqueness remains refuted
for directed systems. The finite census is executable in
`scripts/enumerate_program_m_relations.py`; extension beyond four objects and a
Lean-certified enumeration remain **O**.
The order-theoretic skeleton compiles in
`JanusFormal.Foundations.ProgramMCausalSkeleton`. Its interpretation as
physical causality remains **O**.
The lossless decorated skeleton compiles in
`JanusFormal.Foundations.ProgramMDecoratedSkeleton`. Minimal decoration and
physical throat interpretation remain **O**.
The controlled finite compression audit is executable through
`scripts/enumerate_program_m_relations.py`. A general characterization of which
observables factor through a chosen compression remains **O**.
The general factorization criterion compiles in
`JanusFormal.Foundations.ProgramMObservableFactorization`. Concrete physical
observables and their factorization proofs remain **O**.
The local-finiteness gate and finite-census no-go compile in
`JanusFormal.Foundations.ProgramMCausalSetKinematics`. Physical causal
interpretation and infinite-limit control remain **O**.
The dimension-invariant census is executable through
`scripts/enumerate_program_m_relations.py`. Manifold-likeness, estimator
convergence and emergent dimension remain **O**.
The coordinate-blind Myrheim–Meyer audit runs in
`scripts/audit_program_m_blind_dimension.py`. Its held-out finite gate passes,
but the grid collision proves that this estimator alone does not establish
manifold-likeness or geometric dimension.
The coordinate-blind interval-abundance audit runs in
`scripts/audit_program_m_interval_abundance.py`. It closes its finite held-out
discrimination gate; sufficiency, multi-scale stability and analytic
convergence remain **O**.
The multi-scale extension runs in
`scripts/audit_program_m_interval_multiscale.py`. Its global gate is **not**
closed: validation acceptance is 87.5% at `N=256` versus a fixed 90% minimum.
The fresh conformal successor runs in
`scripts/audit_program_m_interval_conformal.py`. All finite gates pass and the
per-scale marginal coverage guarantee is 90% under exchangeability. This is
not a manifold-likeness probability or a simultaneous multi-scale guarantee.
The reusable candidate reporter runs in
`scripts/evaluate_program_m_order_candidate.py`. It does not close the target
embedding, number-volume, chain-time or uniqueness obligations.
The raw-relation adapter runs in
`scripts/evaluate_program_m_relation_candidate.py`. Its cyclic-refinement
collision proves that quotient diagnostics cannot recover primitive edges or
internal cycles.
The order-embedding no-go compiles in
`JanusFormal.Foundations.ProgramMManifoldlikeOrderEmbeddingNoGo`. Faithful
Lorentzian embedding, density control and approximate uniqueness remain **O**.
The preliminary contract compiles in
`JanusFormal.Foundations.ProgramMFaithfulEmbeddingInterface`. Its target is
still an abstract partial order, and its probability bound is metadata rather
than a proved probabilistic model.
The tautological counterconstruction compiles in
`JanusFormal.Foundations.ProgramMFaithfulEmbeddingNoGo`. A Lorentzian target
class and a concrete chain-length/proper-time realization remain **O**.
The strengthened pre-geometric contract compiles in
`JanusFormal.Foundations.ProgramMWellConditionedEmbedding`, reusing Mathlib's
`Set.chainHeight`. A genuine Lorentzian manifold instance, statistical model
and approximate-uniqueness theorem remain **O**.
The external 1+1 test target compiles in
`JanusFormal.Foundations.ProgramMMinkowskiTwoTarget`. No Program M candidate
embedding into it has yet been certified.
The exact finite audit runs in `scripts/enumerate_program_m_relations.py`.
For the three-chain witness it also checks every endpoint diamond with density
2, count tolerance 1, exact chain-step/time conversion and zero time tolerance.
This finite deterministic check is not a statistical continuum certificate.
The scaling audit is emitted by the same script. It separates macroscopic
number-volume convergence from multidirectional time reconstruction; neither
deterministic family closes the full continuum gate.
The separate Poisson audit runs in
`scripts/audit_program_m_poisson_minkowski2.py`; all preregistered finite-sample
gates pass. Asymptotic convergence, a Lean probability proof and emergence
from the primitive relation remain **O**.
The rank-embedding uniqueness audit runs in
`scripts/audit_program_m_embedding_ambiguity.py`. Its four-object witness
refutes uniqueness for the current linear-extension-rank reconstruction, not
for all possible continuum reconstruction methods.
The separated number-volume selection audit runs in
`scripts/audit_program_m_volume_selection.py`. At five objects it uniquely
selects 2 of 10 ambiguous classes and leaves 8 unresolved, so it is useful but
not sufficient for geometric uniqueness.
The chain-time successor runs in
`scripts/audit_program_m_chain_time_selection.py`. It selects the opposite
rank realization in exactly the two cases selected by number-volume, leaving
no jointly Pareto-dominant candidate through five objects.
The scalarisation no-go compiles in
`JanusFormal.Foundations.ProgramMTradeoffNoGo`. It proves that the first exact
conflict cannot be turned into an intrinsic winner by an unnormalised weighted
sum.
The dimensionless successor runs in
`scripts/audit_program_m_scale_consistency.py` and its exact witness compiles in
`JanusFormal.Foundations.ProgramMScaleConsistencyNoGo`. Zero finite tolerance
is not promoted into a statistical rejection of an asymptotic target law.
The finite-sample calibration runs in
`scripts/audit_program_m_scale_conformal.py`. Its marginal conformal guarantee
does not repair sufficiency: every preregistered square grid attains exact zero
score and is accepted.
The local fluctuation successor runs in
`scripts/audit_program_m_count_fluctuations.py`. It rejects the retained grids
and diagonal controls, but still depends on an external null-coordinate cell
partition and is not promoted to a coordinate-free geometric certificate.
The intrinsic successor runs in
`scripts/audit_program_m_intrinsic_link_fluctuations.py`. Its statistic is
exactly invariant under relabelling and global orientation reversal and rejects
the current grids/chains, but sufficiency against matched adversaries remains
open.
The first adversarial search runs in
`scripts/audit_program_m_adversarial_orders.py`. It proves by counterexample
that MF-MAN-015 alone is insufficient; all 400 tested candidates are nevertheless
rejected by the frozen three-gate intersection.
The targeted successor runs in
`scripts/audit_program_m_twin_adversary.py`. It breaks that intersection with
101/240 fresh engineered candidates, including a passing twelve-object twin
class; the combined gate is therefore not a certificate of generic geometry.
The exact-twin repair runs in `scripts/audit_program_m_exact_twins.py`; its
Poisson-calibrated threshold rejects the named exact clones without banning
natural pairs. The follow-up `scripts/audit_program_m_branch_adversary.py`
breaks this repair using repeated two-level suborders with distinct exact
past/future signatures.
The WL generalization runs in `scripts/audit_program_m_wl_compressibility.py`
and detects both registered symmetric attacks. Its asymmetric counterattack in
`scripts/audit_program_m_wl_adversary.py` passes all five gates with a short
graduated-chain generator, proving that stable color multiplicity is not a
general compression certificate.
