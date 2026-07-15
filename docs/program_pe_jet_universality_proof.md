# Program P.E-J — Finite-Jet Universality and Categorical Scope

> Master project map: [`program_master_roadmap.md`](program_master_roadmap.md)  
> Precise Lemma 2: [`program_pe_lemma2_naturality_equivariance.md`](program_pe_lemma2_naturality_equivariance.md)  
> Corrected category theorem: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)

## Question

Can one prove that every local natural theory attached to a decorated SpinC
immersion is determined, up to natural equivalence, by equivariant data of a
finite jet?

## Verdict

The original sentence is too strong. The strongest defensible
operator-by-operator theorem is:

> **Corrected local finite-jet universality theorem.** Fix natural source and
> target bundles over a category of decorated SpinC immersions. A regular local
> natural operator is locally represented by a smooth map from a finite jet
> bundle. Once holonomic jets are realizable, that representing map is unique,
> and naturality of the operator is equivalent to equivariance of the jet map
> under a sufficiently high adapted jet symmetry presentation. For scalar
> targets the map is an invariant smooth function; for nontrivial targets it is
> an equivariant covariant.

Five qualifications are essential:

1. Peetre–Slovák gives local finite order under regularity and locality;
2. one uniform global order requires an additional compactness/boundedness or
   finite-cover hypothesis;
3. smooth equivariant dependence is not automatically polynomial;
4. naturality does not imply ellipticity or select field bundles;
5. a category of operators requires morphisms from jet prolongations and
   holonomic composition, not ordinary maps between unprolonged representation
   fibers.

For ordinary natural and gauge-natural bundles, the finite-order categorical
classification is a classical external theorem. For decorated Janus SpinC
immersions, the structured jet groupoid, descent theorem and global/local split
remain open.

## Proof architecture

### 1. Peetre–Slovák reduction

For a regular local sheaf morphism

```text
D : Gamma(F) -> Gamma(E),
```

Peetre–Slovák supplies locally an order `k` and smooth evaluator

```text
Phi : J^k(F) -> E
```

such that

```text
D(s)(x) = Phi(j_x^k s).
```

This analytic theorem is used as an external interface and is not reproved in
Mathlib.

The conclusion is local finite order near a chosen infinite jet. It is not one
universal order on every component of an arbitrary configuration space.

### 2. Naturality implies equivariance

Choose an adapted frame and compatible actions on sections, jets and targets.
If jet realization is surjective and

```text
D = Phi o j^k,
```

then

```text
D natural  <->  Phi equivariant.
```

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .operator_natural_iff_evaluator_equivariant
```

The exact intrinsic/fiber-model statement and the order qualification for the
adapted jet symmetry presentation are documented separately in
`program_pe_lemma2_naturality_equivariance.md`.

### 3. Uniqueness

If two evaluators represent the same operator and every finite jet is
holonomically realizable, evaluate on a section realizing an arbitrary jet. The
evaluators agree everywhere.

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .evaluator_unique_of_surjective_jet
  .exists_unique_equivariant_evaluator
```

### 4. Local-to-uniform order

A finite collection of local orders has a common upper bound and lower-order
evaluators lift by jet truncation. An infinite family of componentwise finite
orders need not have one global bound.

Lean:

```text
P0EFTJanusFiniteOrderUniformization
  .lifted_evaluator_factorization
  .finite_local_orders_have_common_bound
  .componentwise_finite_order_has_no_uniform_bound
```

Thus the finite-order category must either restrict to operators with a declared
global order on the chosen region or be replaced by an infinite-jet/pro-object
category with locally cylindrical morphisms.

### 5. Scalar invariants versus covariants

For a trivial scalar target:

```text
Phi(g.j) = Phi(j).
```

For tensor, spinor or ghost targets:

```text
Phi(g.j) = g.Phi(j).
```

The second case is equivariant/covariant, not scalar-invariant.

### 6. Smooth is not automatically polynomial

The order-zero natural scalar operation

```text
D(s)(x) = exp(s(x))
```

is smooth and local but nonpolynomial. The Lean model proves

```text
Delta^n exp(x) = (exp(1)-1)^n exp(x),
```

so no finite forward difference vanishes.

Lean:

```text
P0EFTJanusSmoothNotPolynomial.lean
```

### 7. Ellipticity is independent

The zero operator is natural but has a noninjective symbol. Thus finite-jet
naturality does not imply ellipticity.

Lean:

```text
P0EFTJanusCorrectedJetUniversality
  .naturality_does_not_imply_symbol_injectivity
```

### 8. Composition requires holonomic prolongation

Suppose a first operator has an order-`k` evaluator and a second has an
order-`l` evaluator:

```text
phi : J^k E -> F,
psi : J^l F -> G.
```

Their composite is not represented by the plain function composition
`psi o phi`, because `psi` expects an `l`-jet of an `F`-section. The correct map
uses the holonomic prolongation

```text
J^(k+l) E
  -> J^l(J^k E)
  -> J^l F
  -> G.
```

Lean:

```text
P0EFTJanusJetOperatorComposition
  .composite_operator_factors_through_higher_jet
```

This abstract theorem is the formal reason the proposed right-hand category is
co-Kleisli-like: morphisms start from jet prolongations, and composition raises
jet order.

## Exact theorem currently formalized

Given:

- compatible actions on sections, jets and targets;
- equivariant jet prolongation;
- surjective jet realization;
- a factorized operator;

the repository proves:

```text
operator natural
  iff
unique jet evaluator equivariant.
```

Given in addition an abstract holonomic prolongation compatible with the first
operator, it proves that a composite operator factors through the corresponding
higher source jet.

Stable head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

## Categorical theorem: proved externally, not reconstructed in Lean

For fixed base dimension, finite-order natural bundles are associated to smooth
actions of finite jet groups. A finite-order natural differential operator is
canonically represented by a smooth equivariant map from the standard fiber of
a jet prolongation. Conversely, such an equivariant map descends to a natural
operator.

The resulting category has:

```text
objects: smooth finite-order jet-group actions;
morphisms S -> T: equivariant maps J^k S -> T for some finite k;
composition: holonomic prolongation;
identities: order-zero identity maps.
```

For gauge-natural bundles the finite jet group is replaced by the principal
prolongation group. This is the classical Kolář–Michor–Slovák theorem,
categorically repackaged in the companion document.

The repository's Lean code currently proves only finite algebraic cores of this
architecture. It does not formalize smooth manifolds of jets, associated-bundle
descent or the full category equivalence.

## Why the Janus side should be a groupoid

A fixed representation group is generally insufficient when the background jet
varies. Let `B_R` be the space of admissible jets of the immersion, metrics,
connections, SpinC data and declared discrete decorations. Coordinate, frame
and gauge transformations form a groupoid

```text
Gamma_R ==> B_R.
```

Natural field sectors should be equivariant bundles over `B_R`. Curvature,
second fundamental form and twist curvature distinguish orbits, while isotropy
groups can jump. The Janus equivalence therefore requires a structured jet
groupoid and effective descent, not merely one linear representation category.

Global topology remains separate: point jets do not reconstruct holonomy,
SpinC classes, a chosen square-root line, a `Z4` lift, determinant-line holonomy
or nonlocal spectral operators.

## Finite generation is not a consequence of equivariance

Even for finite-dimensional jet spaces, smooth equivariant-map spaces are
usually infinite-dimensional. Polynomial invariant rings are not automatically
finitely generated for arbitrary nonreductive group actions, and higher jet
groups contain nonreductive parts.

A viable finite-generation theorem requires an additional reduction:

```text
structured jet normal form
  -> compact/reductive residual group
  -> polynomial invariant generators
  -> smooth invariant/equivariant module theorem.
```

For compact linear actions, Hilbert-type finite generation and the Schwarz
theorem control smooth scalar invariants. Extension across constrained jet loci
and isotropy strata remains a separate theorem. Pseudo-Riemannian signatures
require additional work because the residual orthogonal group is noncompact.

## Scoped follow-on descent results

In the low-order Euclidean model, all valid projected-seed chart jets at one
fixed base lie in the same residual SpinC-frame orbit. Consequently every
invariant observable has a unique chart-independent value there.

Two further Cech constructions are conditional. Supplied oriented transition
cocycles, Spin lifts, phases and matching diagonal defects determine a
multi-chart pointwise SpinC transition presentation satisfying the Cech laws;
transition continuity/smoothness and a principal-bundle total space are not
constructed. Supplied local abelian
potentials and additive overlap shifts satisfy the affine derivative law. When
all overlap shifts are curvature-flat, their local curvatures glue uniquely to
a global smooth curvature function. Neither theorem derives these inputs from actual Janus
characteristic classes or determinant transitions.

## Janus specialization still open

1. Define the actual category of decorated Janus SpinC immersions.
2. Construct the structured finite jet groupoid, including tangent/ambient
   frame, SpinC/U(1), normal `Z4`, PT and BRST/Grassmann data.
3. Prove effective descent for the declared natural field bundles.
4. Verify sheaf locality and regularity for each operator.
5. Specialize Peetre–Slovák to the chosen category.
6. Prove holonomic realization for the required constrained jet fibers.
7. Specify a bounded Janus-background region for any uniform-order claim.
8. Formalize the full jet-tower category and its composition laws.
9. Prove a structured jet-normal-form/isomorphism theorem.
10. Classify smooth equivariant maps across all isotropy strata.
11. Add polynomial dependence only for a separately defined polynomial/weighted
    subclass.
12. Impose ellipticity, Helmholtz, anomaly and renormalization independently.

## Evidence matrix

| Claim | Status |
| --- | --- |
| finite-jet naturality/equivariance equivalence | proved in Lean action model |
| evaluator uniqueness under jet surjectivity | proved in Lean action model |
| composite factors through higher jet under holonomic compatibility | proved in Lean abstract model |
| finite local orders admit a common finite bound | proved in Lean model |
| local finite order need not have a global bound | proved in Lean model |
| smooth natural does not imply polynomial | explicit counterexample and Lean finite-difference proof |
| classical natural/gauge-natural categorical theorem | external theorem; documented, not formalized in Lean |
| Peetre–Slovák for actual Janus category | analytic interface; specialization open |
| Euclidean Koszul connection from a positive metric | proved constructively in Lean |
| projected-seed varying normal atlas | proved in Lean with smooth overlap laws |
| one-chart rank-two SpinC bundle/connection | proved in Lean; nontrivial global sectors open |
| valid-chart low-order residual/SpinC action groupoid | instantiated in Lean |
| actual valid-chart overlap arrows | proved with identity and Cech composition in the low-order Euclidean model |
| fixed-base low-order invariant-observable descent | proved in Lean; smooth global effective descent remains open |
| multi-chart SpinC Cech transition presentation | conditional pointwise theorem from supplied cocycles, lifts, phases and matching defects; continuity and total space open |
| abelian connection overlap curvature descent | conditional global smooth curvature theorem from supplied local potentials and flat additive shifts |
| actual structured SpinC jet groupoid | open |
| effective Janus descent theorem | open |
| full smooth equivariant-map classification | open |
| finite generator theorem | conditional on normal form and residual invariant theory |
| polynomial invariant classification | conditional on polynomial dependence |
| ellipticity | independent open theorem |

## Final statement

```text
regular + local + natural
  -> locally finite-jet
  -> unique smooth equivariant evaluator on realizable jets.

finite-order operator category
  -> jet-prolonged equivariant morphisms
  -> holonomic composition.
```

Global order, polynomiality, finite generation, ellipticity, global topology and
field-content selection remain separate hypotheses or theorems. The classical
category equivalence is known for ordinary natural/gauge-natural bundles; its
structured Janus SpinC-immersion specialization is not yet proved.

## Primary references

- J. Navarro and J. B. Sancho, *Peetre–Slovák's theorem revisited*.
- I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*.
- J. Navarro and J. B. Sancho, *Natural operations on differential forms*.
- G. W. Schwarz, *Smooth functions invariant under the action of a compact Lie group*.
- M. Nagata, *Lectures on the Fourteenth Problem of Hilbert*.
