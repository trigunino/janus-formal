# Program P — Variational Principle and Action Reconstruction

> Current integration and CI truth: [`current_status.md`](current_status.md)  
> Master dependency map: [`program_master_roadmap.md`](program_master_roadmap.md)

## 1. Research question

Programs D8–D11 identify candidate topology, natural bundles, spectral symbols and determinant-line interfaces. None of those data selects one physical Janus action.

Program P asks:

> How can a concrete Janus Euler–Lagrange system and action be selected or reconstructed without fitting the desired radius, vacuum or finite counterterms?

The mature architecture is:

```text
P0   prove what cannot select the action
P-A  characterize an action relative to a specification or parent theory
P-B  impose anomaly and discrete consistency
P-C  solve the inverse variational problem by Helmholtz conditions
P-D  classify invariant pairings and residual couplings
P-E  reduce regular local natural data to finite-jet equivariant evaluators
P-F  pull a target pairing back through compatibility maps and derive Noether structure
```

The subprograms are complementary. They are not a sequential proof in which each earlier route is sufficient by itself.

## 2. Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | exact theorem/algebra checked in Lean |
| **X** | executable Python/SymPy audit |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic or geometric theorem represented by an interface |
| **N** | no-go result or correction |
| **O** | open Janus construction or theorem |

## 3. P0 — Moduli geometry no-go

Finite models prove:

```text
same metric      + different potentials,
same metric      + different gradients,
same symplectic  + different Hamiltonians.
```

Therefore:

```text
(moduli, metric, symplectic form, complex structure)
  does not determine
one action.
```

A Kähler-like structure may organize gradient or Hamiltonian flows. It does not supply the moment map or functional.

**Lean:** `P0EFTJanusModuliGeometryNoGo.lean`  
**Verdict:** **T/N**; the earlier idea that rich moduli geometry alone forces the action is rejected.

## 4. P-A — Relative universal property and parent reduction

### 4.1 Quadratic action theorem

For

```text
S(x) = h*x^2/2 + l*x + c,
```

the Hessian fixes only `h`. Actions with the same Hessian differ by an affine functional.

A unique normalized representative is obtained after specifying:

1. Hessian `h`;
2. critical point `x_*`;
3. reference value `S(x_*)`.

This yields a nonempty subsingleton realization fiber in the finite model.

**Lean:** `P0EFTJanusUniversalActionProperty.lean`  
**Evidence:** **T**.

### 4.2 Parent-bulk realization

For a quadratic bulk variable `X` and throat variable `q`,

```text
S(X,q) = A*X^2/2 + B*X*q + C*q^2/2,
X_*(q) = -B*q/A,
S_red(q) = (C - B^2/A)*q^2/2.
```

The reduced Hessian is a Schur complement. In a PDE theory, the analogue is a Dirichlet-to-Neumann/Calderón operator plus local boundary terms.

**Lean:**

```text
P0EFTJanusBulkReducedPotential.lean
P0EFTJanusBulkUniversalHelmholtzSynthesis.lean
P0EFTJanusParentBulkHelmholtzReciprocity.lean
P0EFTJanusFiniteRankParentSchurHelmholtz.lean
```

**Evidence:** **T/C**.

The finite two-sector synthesis proves uniqueness of the stationary bulk mode,
the exact Schur-complement on-shell action, and reciprocal PT-even reduced
Hessian. A pair of explicit parents also shows that equal reduced diagonal
terms do not fix the surviving same-parity mixing.

The finite-rank extension permits any finite boundary index and proves the
exact on-shell reduction, symmetric Schur kernel and pairing-level
self-adjointness. It also proves that the bulk Euler expression is the actual
derivative of the parent action and computes the Fréchet derivative and
constant Hessian of the reduced action. Exact square completion classifies the
stationary bulk value, at fixed boundary data, as the unique global minimum
for a positive bulk coefficient and the unique global maximum for a negative
one. It remains finite-dimensional, not a Janus bulk PDE.

A concrete one-dimensional bridge to the positive PT-flat proportional
bimetric branch proves the actual derivative of the reduced interaction,
stationarity at `c = 1`, and an actual Hessian equal to twelve times the
Fierz--Pauli mass combination. For `beta1 > 0`, `beta2 >= 0`, that Hessian is
positive and `c = 1` is the unique global minimizer on `c > 0`. This does not
establish a variational principle or stability theorem on the full Janus metric
field space.

This proportional information does not reconstruct transverse dynamics. A
quadratic extension and its `lambda * y^4` deformation have exactly the same
restriction at `y = 0`, the same genuine longitudinal derivatives and the same
complete transverse two-jet, with Hessian `2 kappa`, all along that branch. For
nonzero `lambda` they are nevertheless distinct off branch. Thus even the local
transverse Hessian does not determine the nonlinear extension. This is a
reduced reconstruction no-go, not a candidate full metric action.

**Lean:** `P0EFTJanusPTFlatBimetricVariationalBridge.lean`,
`P0EFTJanusProportionalBranchTransverseNoGo.lean`,
`P0EFTJanusProportionalBranchHigherOrderNoGo.lean`
**Evidence:** **T/C** on the one-dimensional proportional branch and **T/N**
for reconstruction of a transverse extension from that branch alone.

### 4.3 Reduced two-metric action, boundary and spectrum audit

The M30 action writes two Einstein--Hilbert sectors plus matter and cross
densities, but does not specify the cross densities as functionals. The new
formal result therefore uses an explicit reduced candidate and does not
attribute that candidate to M30. Its homogeneous exchange-symmetric
interaction restricts exactly to the audited PT-flat proportional potential.
For arbitrary independent scale variations, the bulk, interaction and two
linear boundary channels have the displayed genuine directional derivative;
stationarity is equivalent to both reduced Euler components vanishing. Since
unspecified boundary coefficients can stationarize any scale pair, the bulk
candidate cannot select a scale before the physical GHY/null/worldvolume
functional is derived.

A separate quadratic two-mode candidate has genuine first and second Frechet
derivatives. Positive kinetic coefficients and nonnegative relative mass give
a positive reduced Hessian. The interaction Hessian has exactly the diagonal
kernel and descends to a positive algebraic relative-sector quotient for
positive PT-flat mass. Conversely, the reduced pure-kinetic action with the
published relative sign `kappa = -1` has a strictly negative actual Hessian
direction in an ordinary positive-Hilbert interpretation. This is a reduced
sign obstruction, not a full covariant ghost theorem.

**Lean:** `P0EFTJanusReducedTwoMetricBoundaryFirstVariation.lean`,
`P0EFTJanusReducedBimetricQuadraticFrechetSpectrum.lean`
**Evidence:** **T/C/N** in the declared reduced sectors.

### 4.4 Abstract bulk/boundary variational domain

A normed-space trace/lift interface now separates interior variations from an
arbitrary submodule of admissible boundary modes. The sector action has its
genuine Frechet derivative, and stationarity on admissible variations is
equivalent to both the interior bulk equation and cancellation of the lifted
bulk contribution by the boundary flux. The theorem extends to two independent
sectors. If a bulk-on-shell sector has an accessible nonzero boundary flux,
stationarity is impossible. The trace, lift and boundary action are supplied
analytic data: no GHY, null, corner or junction functional is constructed.

**Lean:** `P0EFTJanusTwoSectorBulkBoundaryFrechetVariation.lean`
**Evidence:** **T/C** for the declared normed variational interface.

### 4.5 Boundary completion and induced-field variation

For a supplied differentiable boundary flux with symmetric actual Jacobian,
the negative radial primitive is a genuine counterterm with derivative exactly
minus that flux. It cancels an exact supplied boundary one-form, is unique up
to a constant, becomes unique after base normalization, and a non-Helmholtz
flux obstructs any global `C^2` counterterm of this type. This is an acceptance
criterion; it does not derive a bulk flux or construct GHY/null/corner data.

If a second field is induced from the bulk field, the correct Euler one-form
is the chain-rule combination `E_bulk + E_induced ∘ D(induced)`. Requiring
both terms to vanish separately is stronger. The action `S(x,y)=x-y`
restricted to `y=x` has zero actual derivative although both artificial
independent Euler equations are nonzero.

**Lean:** `P0EFTJanusBoundaryCountertermHelmholtz.lean`,
`P0EFTJanusInducedFieldVariationNoDoubleCounting.lean`
**Evidence:** **T/C/N** for supplied normed-space flux and induced-field data.

### P-A verdict

A parent variational problem gives a canonical throat action **relative to that parent problem**. Different parent actions, normalizations or boundary terms give different reduced actions.

**Open:** derive one actual bulk/junction action and its admissible boundary problem without target-scale input.

## 5. P-B — Anomaly consistency and discrete selection

### 5.1 Positive result

PT pairing reverses the parity-odd anomaly proxy, so the paired proxy cancels.
A separate finite-mode heat-kernel regulator now computes an actual chiral
trace for nonnegative squared spectrum and regulator time: the isospectral
opposite-chirality PT partner cancels it at every time while the parity-even
heat trace doubles. This is not yet the continuum Janus anomaly.

### 5.2 No-go result

PT pairing preserves and doubles parity-even couplings and finite even counterterms. Two actions can both be anomaly-free while having different parity-even dynamics. A flat determinant line may still admit multiple trivialization phases.

### 5.3 Conditional discrete selection

Given externally fixed regulator arithmetic, a minimal half-level condition may select a multiplicity. Such a result is conditional on the regulator level, statistics and field content.

**Lean:**

```text
P0EFTJanusAnomalySelection.lean
P0EFTJanusAnomalyHelmholtzIndependence.lean
```

Four explicit finite candidates realize all truth patterns of the anomaly and
Helmholtz filters. This proves both non-implications and their joint
compatibility in the declared algebraic proxy, not the anomaly of Janus.

### P-B verdict

Anomaly cancellation is an independent consistency filter and sometimes a discrete selector. It does not reconstruct the parity-even action and does not replace Helmholtz.

## 6. P-C — Helmholtz inverse variational problem

### 6.1 Quadratic theorem

For a finite linear two-field system, existence of a quadratic potential is equivalent to formal self-adjointness of the Hessian matrix.

```text
H_xy = H_yx
  <->
H is a quadratic Hessian.
```

A nonsymmetric operator is not variational. Equal Hessians differ by affine terms. PT-evenness around the selected background removes linear terms, and one reference normalization removes the constant.

**Lean:** `P0EFTJanusHessianHelmholtzReconstruction.lean`  
**Evidence:** **T**.

### 6.2 Coupled-sector theorem

In the finite normal/trace/PT-odd model:

- Helmholtz imposes reciprocal cross couplings;
- a linear operator is the Hessian of a PT-invariant quadratic potential iff
  it is reciprocal and its two even-to-odd coefficients vanish;
- PT forbids even–odd quadratic mixing;
- same-parity normal–trace mixing remains free;
- fixed diagonal symbols + Helmholtz + PT do not select a unique action.

**Lean:** `P0EFTJanusCoupledSectorHelmholtzSelection.lean`  
**Evidence:** **T/N**.

### 6.3 Polynomial nonlinear theorem

For a finite quadratic Euler source in two variables, equality of cross derivatives is equivalent to explicit coefficient relations. Under those relations a cubic potential is reconstructed.

**Lean:** `P0EFTJanusPolynomialHelmholtzReconstruction.lean`  
**Evidence:** **T** in the polynomial proxy.

At arbitrary finite coefficient rank, an affine/quadratic Euler family is the
formal gradient data of linear/quadratic/cubic potential coefficients exactly
when linear reciprocity and the quadratic Helmholtz swap hold. The normalized
finite-sum potential has this gradient as its actual Fréchet derivative, so the
reconstructed derivative pairs with the Euler source in every direction. The
actual Euler map also has the displayed Jacobian as its Fréchet derivative,
and the coefficient Helmholtz swaps make that Jacobian self-adjoint in the
finite coordinate pairing. Conversely, self-adjointness of this actual
Jacobian recovers both coefficient swaps by testing zero and coordinate-basis
fields. Conversely, equality of the genuine derivative with the prescribed
Euler pairing at every field value alone recovers the normalized affine,
quadratic and cubic potential coefficients.

**Lean:** `P0EFTJanusFiniteRankPolynomialHelmholtz.lean`
**Evidence:** **T** coefficient-level; no global variational cohomology.

More generally, on an open convex real normed configuration domain, a
differentiable Euler one-form with symmetric actual Jacobian admits a scalar
action whose Fréchet derivative is that one-form. On the whole space, the
straight-segment integral gives an explicit primitive normalized at a chosen
base point. Any two such actions on a nonempty convex domain differ by a
constant, so fixing one base value removes this ambiguity. This is a
configuration-space Poincaré lemma, not the local PDE variational bicomplex.
If the domain is the whole configuration space and an action has the supplied
Euler one-form as its actual derivative everywhere, additive linear gauge
invariance is equivalent to Euler horizontality. In particular, the normalized
radial primitive built from horizontal Euler data is invariant along all
corresponding affine gauge orbits. This is a conditional linear Noether model.
For a supplied complete differentiable one-parameter flow, the analogous
nonlinear statement is exact: full-orbit invariance is equivalent to the actual
Euler derivative annihilating the field-dependent generator everywhere, and
horizontal Helmholtz data reconstruct an invariant normalized radial action.
The full orbits of the supplied flow form a set quotient. For any target type,
pullback and descent give an equivalence between functions on that quotient and
configuration-space functions invariant under the flow. Real-valued functions
specialize this equivalence to invariant actions, including the reconstructed
radial action. No topology or smooth structure is constructed on this quotient.
Separately, real translation of the actual D8 mapping-torus coordinate now
gives a nontrivial complete analytic Janus flow with diffeomorphic time slices
and a jointly analytic action map `ℝ × D8 → D8`.
The flow restricts analytically to the throat, preserves its inclusion, and
pullback gives an exact complete action on all eight blocks of the current
independent-field package, including group/inverse laws, PT conjugation and
compatibility with all five induced fields. A descended periodic cosine field
has a distinct half-period pullback; embedded in the matter sector it gives a
complete `IndependentFields` configuration with a distinct half-period image.
The corresponding orbit setoid and quotient are now instantiated
on that complete field package, and quotient functions are exactly invariant
field functions; no topology is placed on the orbit space. It is not yet the flow of an
arbitrary ghost, a gauge group, or a PDE identity with boundary terms.

**Lean:** `P0EFTJanusConvexHelmholtzReconstruction.lean`,
`P0EFTJanusLinearGaugeNoetherReconstruction.lean`,
`P0EFTJanusNonlinearGaugeFlowNoether.lean`,
`P0EFTJanusGaugeOrbitDescent.lean`,
`P0EFTJanusGaugeOrbitInvariantEquiv.lean`,
`P0EFTJanusMappingTorusCompleteTimeFlow4D.lean`,
`P0EFTJanusMappingTorusJointAnalyticTimeAction4D.lean`,
`P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D.lean`,
`P0EFTJanusMappingTorusNontrivialFieldTimeAction4D.lean`,
`P0EFTJanusMappingTorusIndependentFieldOrbitQuotient4D.lean`
**Evidence:** **T/C** on open convex domains and, on the whole space, for
additive linear or supplied complete nonlinear gauge-flow models; **T/C** for
the concrete nontrivial complete analytic D8 time flow and its complete action
on the current independent-field package, including a nontrivial full-package
field orbit.

For a supplied reduced two-metric chart, the explicit relative quadratic
interaction now has its genuine Frechet derivative. Independent plus/minus
variations recover both Euler components; diagonal and sign-linked variations
recover respectively their sum and difference. Finite diagonal translation
invariance implies the corresponding reduced Noether identity. This does not
construct the covariant diagonal diffeomorphism, Bianchi identity or published
nonlinear cross density.

**Lean:** `P0EFTJanusReducedTwoMetricEulerNoether.lean`
**Evidence:** **T/C** in the supplied reduced chart.

The cross-matter test is now upgraded from a rectangular path proxy to a true
second-variation criterion. In a supplied three-direction chart, one common
`C^2` action forces reciprocity of metric--metric, plus--matter and
minus--matter blocks. Conversely, reciprocal blocks construct an explicit
bilinear common action with the proposed genuine Frechet gradient. Any supplied
nonreciprocal block therefore rules out such an action. M30 leaves the two
interaction densities and their matter dependence unspecified, so this gate
does not assign a mismatch or contradiction to the paper.

On the full product of plus, minus and matter normed spaces, the nonlinear
test has six blocks: three diagonal symmetries and three cross reciprocities.
They are pointwise equivalent to symmetry of the actual total Euler
derivative. On an open convex domain they reconstruct a normalized common
action, unique after normalization. A genuinely supplied failed cross block
rules out a global `C^2` common action. This is a configuration-space
primitive, not a local covariant density attributed to M30.

For a genuine common reduced action invariant under diagonal translation, the
strongest identity with supplied boundary data is
`E_plus + E_minus + boundary_flux = 0`. Separate sector conservation is
equivalent to zero exchange and zero boundary flux. The exact relative-mode
example `(E_plus,E_minus,B) = (1,-1,0)` proves that combined Noether balance
alone does not imply separate conservation. No spacetime diffeomorphism,
Stokes theorem or contracted Bianchi identity is claimed.

For a supplied field-dependent diagonal generator `K(q)`, the derivative
along the frozen infinitesimal gauge line proves the exact equivalence between
infinitesimal invariance, Euler annihilation and the formal pullback constraint
`E(q) ∘ K(q) = 0`. The constraint is stable under maps of gauge parameters.
A real counterexample again shows that the combined identity need not split
into sector identities. No complete flow, Janus diffeomorphism generator or
covariant Bianchi divergence is constructed.

**Lean:** `P0EFTJanusReducedCrossMatterIntegrability.lean`,
`P0EFTJanusNonlinearCrossDensityHelmholtz.lean`,
`P0EFTJanusReducedDiagonalNoetherExchangeBalance.lean`,
`P0EFTJanusDiagonalGaugeNoetherIdentity.lean`
**Evidence:** **T/C/N** in the supplied normed spaces and reduced charts.

### 6.4 Global field-theory obligations

The concrete Janus action requires more than finite formal self-adjointness:

1. complete local Euler source;
2. gauge and Noether identities;
3. nonlinear Helmholtz conditions;
4. vanishing of the relevant variational-bicomplex obstruction;
5. classification of null Lagrangians and boundary functionals;
6. PT/discrete symmetry constraints;
7. normalization and finite counterterm law;
8. globalization over the actual field space.

### P-C verdict

P-C is the strongest inverse route. It reconstructs an action class from a compatible Euler family; it does not choose the Euler family or the surviving finite data.

## 7. P-D — Invariant pairings

P-D replaces arbitrary residual coefficients by representation-theoretic spaces:

```text
Hom_G(E_i tensor E_j, scalar).
```

Low-rank results presently formalized or audited include:

- same-quarter `Z4` quadratic terms are forbidden;
- conjugate `(+i,-i)` quarter sectors admit one cross pairing up to scale;
- an uncharged PT doublet retains diagonal/cross multiplicity freedom;
- scalar–vector, scalar–traceless and vector–traceless scalar pairings vanish;
- vector self-pairing is unique up to scale;
- signed permutations leave two traceless-tensor forms;
- a generic continuous rotation reduces the traceless-tensor pairing to the Frobenius contraction up to scale;
- repeated irreducibles leave multiplicity-space matrices.

**Lean/Python:** P-head pairing gates, `FundamentalGeometryPEInvariantPairings/Gates/`, and `audit_janus_pe_*pairings.py`.

### P-D verdict

P-D decides whether a coupling is forbidden, multiplicity-one or multi-parameter. It does not fix the normalization of a surviving one-dimensional invariant or a repeated-irrep multiplicity matrix.

## 8. P-E — Corrected finite-jet universality

The original claim that every natural operator is polynomial in one finite jet is too strong.

The defensible theorem architecture is:

```text
regular + local
  -> locally finite-jet                         [Peetre–Slovák interface]

finite-jet presentation + naturality
  <-> smooth equivariant evaluator              [formal action model]

surjective holonomic realization
  -> evaluator uniqueness.
```

The evaluator is smooth, not automatically polynomial. Local finite order need not have a global uniform bound. Naturality does not imply ellipticity or field-content selection.

**Lean head:**

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

**Current merged status:** PR 10 is on `main`. Its theorem head builds locally
with constructive Euclidean Koszul existence, projected-seed varying-normal
transitions, one-chart rank-two SpinC connection data and a valid-chart
low-order residual/SpinC action groupoid. Independent post-merge remote CI is
not claimed here.

**Active follow-on scope:** at one fixed Euclidean base point, invariant
low-order observables have a unique value independent of the valid
projected-seed chart. When an observable admits a smooth realization on the
continuous reduced coefficients, these values form a globally smooth function
by local fixed-chart gluing. Separately, supplied multi-chart oriented cocycles, Spin
lifts, phases and matching defects are packaged as a pointwise SpinC Cech
transition presentation; no transition continuity/smoothness or principal
bundle total space is constructed. Supplied local abelian potentials and
additive gauge shifts give affine connection descent and a unique global smooth
curvature function when all overlap shifts are flat. The derivative of that
descended curvature also obeys the abelian cyclic Bianchi identity. These are
conditional/fixed-base theorems, not full
effective descent or construction of the actual global Janus SpinC bundle and
determinant connection.

On the actual D8 covers, the deck action now forms a category/groupoid whose
source and target components are local diffeomorphisms. Dependent
source/target fibers, a supplied structured-jet representation functor and
unique smooth descent of invariant maps are constructed. Supplied low-order
holonomic families and their `(II,F)` reductions descend smoothly to the true
quotient. This does not yet construct the physical SpinC representation,
higher jets, isotropy strata or a Peetre--Slovák integrability theorem.

### Open Janus specialization

- full adapted SpinC/PT/Z4/BRST jet symmetry group beyond the low-order
  residual/SpinC realization;
- actual source and target natural bundles;
- locality and regularity proof;
- holonomic realization/surjectivity;
- classification of smooth equivariant evaluators;
- separate ellipticity test.

## 9. P-F — Compatibility pullback, Helmholtz and Noether

The speculative implication

```text
Gauss–Codazzi–Ricci–Bianchi compatibility -> Helmholtz
```

is false without additional variational data.

The corrected schema is:

```text
compatibility map K
linearization J
self-adjoint target pairing/Hessian H
              |
              v
pulled-back Hessian J^T H J.
```

In the abstract finite model:

- `J^T H J` is self-adjoint and satisfies quadratic Helmholtz;
- gauge invariance `K R = 0` yields the linearized Noether identity;
- the strong compatibility-complex synthesis also packages `B K = 0`,
  gauge-Hessian degeneracy, compatible gauge variations and restricted
  Helmholtz;
- Helmholtz and Noether remain logically distinct in general;
- in normed spaces with the supplied differentiability hypotheses, the actual
  Fréchet second variation of `L ∘ K` is
  `H(Ju)(Jv) + dL(D²K(u,v))`; it reduces to `H(Ju)(Jv)` when the target
  gradient `dL` vanishes;
- Schwarz symmetry makes the complete actual second variation symmetric even
  off criticality; at a target critical point this proves symmetry of
  `J^T H J` without separately postulating symmetry of `H`;
- a target critical point pulls back to genuine criticality, and the actual
  pullback Hessian annihilates `ker J` in either argument. Consequently it
  annihilates the generated directions `im R` whenever `J ∘ R = 0`. This is an
  abstract normed-space statement, not a concrete Janus field complex;
- for every source submodule contained in `ker J`, this genuine critical
  Hessian descends uniquely as a symmetric bilinear form to the algebraic
  module quotient. Continuity of the descended form and any normed,
  topological or smooth quotient structure are not proved.

**Lean:** `P0EFTJanusFrechetPullbackSecondVariation.lean`,
`P0EFTJanusFrechetPullbackHelmholtz.lean`,
`P0EFTJanusFrechetPullbackGaugeDegeneracy.lean`,
`P0EFTJanusFrechetPullbackQuotientHessian.lean`

**Lean head:**

```text
lake build JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz
```

### P-F verdict

Compatibility geometry can transmit a variational structure supplied by a target pairing/action. It cannot create that pairing from compatibility identities alone.

The synthesis assumes the abstract algebraic complex and target pairing; the
Fréchet theorems likewise supply no concrete compatibility map. They do not
construct the nonlinear Janus compatibility complex or its PDE realization.

## 10. Route matrix

| Route | Proven role | What it cannot do alone |
| --- | --- | --- |
| **P0** | rejects metric/symplectic/Kähler-only selection | choose any action |
| **P-A** | unique action relative to full specification or parent | choose the parent theory |
| **P-B** | anomaly consistency and conditional discrete selection | determine parity-even dynamics |
| **P-C** | reconstruct variational action class from Euler family | choose Euler family or finite scheme |
| **P-D** | classify allowed pairings and multiplicities | normalize surviving invariants |
| **P-E** | reduce regular local natural data to equivariant finite jets | imply polynomiality/ellipticity/field content |
| **P-F** | pull target variational pairing through compatibility map | derive target pairing from geometry alone |

## 11. Best supported synthesis

```text
parent or microscopic law                        P-A
  -> target action/pairing and compatible map
  -> finite-jet equivariant classification       P-E
  -> invariant pairing basis                     P-D
  -> compatible Euler family / pullback          P-F
  -> Helmholtz + variational cohomology           P-C
  -> anomaly consistency                         P-B
  -> normalization + finite counterterms
  -> selected renormalized Janus action.
```

## 12. Precise current frontier

The effective D8 spacetime and fixed-throat quotients now have actual
covering-induced analytic atlases and `IsManifold` instances in dimensions
four and three. Their cover projections are analytic local diffeomorphisms,
and time reversal is an analytic involutive diffeomorphism on both quotients.
The quotient throat inclusion is a closed topological embedding, is `C∞`, has
injective manifold differential everywhere and a rank-one tangent quotient.
Its analytic rank-one normal `VectorBundle` is constructed with one-loop
transition `-id` and pointwise linear equivalences to the differential normal
quotients. Those choices now form a global base-preserving fiberwise-linear
equivalence of dependent total spaces. Transporting the existing normal atlas
through it installs the exact quotient-fiber topology, local trivializations,
`VectorBundle` and analytic `ContMDiffVectorBundle` structures on the
differential normal family; the total comparison is a base-preserving
homeomorphism with the same sign cocycle. The two quarter choices are genuine
global complex line bundles with analytic real underliers and transition
squares equal to the normal sign. The same global winding cocycle now defines
a topological principal normal `Pin⁻(1) ≃ Z4` bundle with equivariant
transitions and free/transitive right action. Applying the two quarter
characters to that cocycle constructs the associated root-phase bundle cores
and recovers their square/PT laws for every winding. The throat inclusion is a
global `IsSmoothEmbedding`, and its normal comparison is an exact fiber-linear
total `Diffeomorph` compatible with the trivializations and sign cocycle.
The differential normal is split intrinsically into a closed zero stratum and
an open nonzero complement, transported exactly by this diffeomorphism.
The actual quotient charts also give the real ambient tangent transitions,
their invertible differentials, nonzero determinants and exact orientation
parity cocycle. Lorentzian null/non-null/joint strata still require a quadratic
reduction. An explicit positive nondegenerate model form is now transported by
each tangent transition with a genuine quadratic isometry; global orthonormal
compatibility remains a contract. The Clifford `spinGroup` now supplies a true
quadratic-preserving vector action and morphism `Spin(Q) →* GL(4)`, with the
twisted Pin extension isolated exactly. Atlas-specific transition lifts,
their Čech cocycle, comparison with the normal lift and SpinC remain open.
For every normed real coefficient fiber, smooth deck-invariant fields on the
analytic cover now descend `C∞` and are exactly equivalent to smooth fields on
this quotient; the flat two-metric/two-scalar/root witness consequently lives
on the actual smooth spacetime. PT pullback and two-sector exchange are exact
involutive equivalences on these smooth coefficient fields. Smooth quotient and throat fields now carry genuine real vector-space structures. The actual compact quotient sends every smooth coefficient field canonically into the completed `L²` space for any finite Borel measure; completeness and the Hilbert structure follow under the explicit complete/Hilbert fiber hypotheses. For a PT-preserving measure, PT pullback is an involutive linear isometry and hence an exact `L²` equivalence. Smooth restriction to the actual throat is defined, linear, PT-equivariant, and yields a nonempty exact PT-compatible Dirichlet subspace. A finite global `C∞` tangent-generating family feeds a complete first-jet graph `H¹` space with dense smooth fields and continuous `L²` forgetting. For throat-supported spacetime measure, its continuous trace has norm bound one. For the canonical physical volumes, the exact FTC/Fubini estimate, twisted analytic latitude collar, throat pushforward and `L²` trace identity are proved. The normal derivative is exactly reconstructed by the finite global frame with an explicit pointwise coefficient bound. Under `CanonicalLatitudeNormalLiftContinuous`, compactness supplies the uniform coefficient and integrability package. The remaining inputs are therefore exactly that tangent-lift continuity and the independent physical coarea bound. Intrinsic Sobolev identification and the resulting physical-volume trace remain open.
The physical coarea chain is now reduced to the pure round-sphere domination
`CanonicalPositiveLatitudeMeasureDomination` for `S² × Ioc(0,1) → S³`.
Product reassociation, the unchanged time factor, exact quotient factorization,
intrinsic-volume pushforward identity, joint collar continuity, frame-energy
integrability, Fubini/map, graph-norm identity and downstream coarea constructor
are proved.
On the complete current independent-field package, PT/exchange also acts on
all componentwise smooth throat boundary data, intertwines the trace exactly
and preserves the full Dirichlet condition.
For the static scalar core, a pointwise uniform graph-ellipticity contract now
implies the energy-to-`H¹` bound and continuous closure bridge, after exact
construction of the Jacobi density root in `L²`. Quantitative control of the
finite tangent frame by holonomic directions is reduced further: uniform
magnitude bounds and holonomic coercivity are automatic, and a purely
geometric coefficient-control contract implies the ellipticity contract. Its
instantiation by a continuous uniformly bounded change of frame remains open.

The reduced candidate, trace/lift, counterterm, induced-field,
nonlinear-cross and infinitesimal-Noether acceptance gates are now explicit;
Candidate A now instantiates part of them.  It supplies reciprocal
four-eigenvalue cross densities, their genuine Frechet Hessian/Helmholtz test,
a pointwise square-root-matrix potential, the actual metric-inverse and
relative-product derivatives followed by an explicit Sylvester inverse on the
open positive diagonal chart, a first-Frechet-differentiable co-diagonal
positive-scale Lorentz root chart with actual metric/inverse/target/root
derivatives and an internally proved Sylvester derivative, together with a
global open connected fixed-frame diagonal 4D Lorentz domain where the
positive principal root exists uniquely, is `C∞`, has an everywhere
invertible Sylvester map and carries the full two-metric derivative including
the inverse-plus contribution. On that entire diagonal domain the genuine
five-coefficient Candidate-A determinant/root/potential chain is now
differentiated in both metric orders and its real two-sector sum is exactly
exchange invariant. The chosen domain is causally compatible through a common
strict timelike direction; its nonnegative closure and exact spectral frontier
are computed. This is still a fixed-frame diagonal sector, not the full
general Lorentz matrix domain. On the actual smooth D8 quotient, two
independent positive diagonal Lorentz metric fields, their unique positive
principal root and the Candidate-A density now use exactly the same global
objects. The local Minkowski IFT root equals that principal root on their
explicit open nonempty diagonal overlap. The density is smooth, obeys the exact manifold chain rule and is
PT/exchange covariant; its integral is invariant under every supplied
PT-invariant Borel measure. Positive exponential curves of those same metric
fields give its pointwise derivative at every parameter and its integrated
functional derivative under an explicit domination contract. This is a genuine curved-base diagonal field functional, not yet a general tensorial action. Intrinsic smooth symmetric covariant two-tensors and their nondegenerate Lorentzian `(3,1)` fiber domains are now defined, and symmetry, nondegeneracy and signature are preserved by fiber pullback. For the actual analytic PT map, this raw tensor pullback and the two-sector exchange are exact involutions; bundling the dependent pullback as a smooth tensor section remains separate. Refining such a metric by its exact musical equivalence now gives the same-tensor inverse contraction, Gram determinant volume, genuine `p=d phi` scalar density and exact pointwise quadratic variation; frame independence, smooth density and integration remain open. On that same quotient, one global independent-field package now contains the two positive diagonal metrics, two matter multiplets, gauge-coordinate pairs, ghosts, auxiliaries, and throat/LL coefficient fields. Metric matrices, the principal root, and matter traces are uniquely induced rather than independently varied. Their simultaneous componentwise variation chain is now exact, including zero induced cross-response from gauge, ghost, auxiliary and LL directions. The abelian `U(1)^2` gauge coordinates are promoted to intrinsic smooth one-forms; `A ↦ A+dλ`, pullback naturality, BRST `s(A,c)=(dc,0)`, nilpotence and the bridge to both independent ghosts are exact. A separate genuine smooth tangent ghost now has exact pullback laws, scalar Lie derivative and a nilpotent linearized BRST complex connected to the independent matter field. Nonlinear graded diffeomorphism BRST, metric Lie derivatives and BV remain open. A finite global `C∞` tangent-generating family closes the frame input of the graph-`H¹` construction; for throat-supported spacetime measure its trace has exact norm bound `1`, while intrinsic Sobolev identification and the physical-volume trace remain open. A global smooth scalar also carries its genuine manifold differential `p = d phi`, with exact throat and PT chain rules. Its fixed-frame diagonal action contracts this differential with the inverse of the same metric, uses that metric's exact volume density, and has exact pointwise and integrated scalar variation at fixed metric/measure under an explicit integrability contract; the covariant Euler--flux equation remains open. A quadratic Robin action built from the actual throat restrictions now yields an exact integrated weak two-sector flux balance and vanishing squared residual at stationary points; geometric normal derivatives and Israel/null junction conditions remain open. Arbitrary smooth diagonal self-diffeomorphisms of the actual spacetime/throat pair now act contravariantly on every independent coefficient sector, preserve positivity, obey the exact identity/composition/inverse laws and commute with smooth throat restriction whenever they preserve the inclusion. A supplied smooth orbit has a genuine manifold tangent generator at time zero. The LL measure/flux coefficients define an actual integrable worldvolume action on the compact throat for every finite Borel measure, and the PT-matched zero configuration is a nonempty zero-action branch. The null counterterm is differentiated on the explicit open admissible domain `Theta ≠ 0`; zero remains excluded by the proved non-differentiability. The candidate
now has a genuine `ZMod 2` exterior coefficient algebra on three odd
generators coupled to the global smooth tangent Lie bracket. The full
three-component ghost has the exact quadratic BRST term; its total cubic
Jacobi obstruction and its induced scalar BRST square both vanish. Three
explicit deck-equivariant spatial rotations now descend with their bracket
table intact, giving an unconditional faithful nonabelian quotient `so(3)`
ghost triple. Its exterior-algebra CE differential is now explicit, odd,
Koszul-Leibniz and square-zero and supplies unconditional closed triple data.
The corrected total convention `D⊗id + action` is globally odd,
Koszul-Leibniz and square-zero and is instantiated without hypotheses. The
legacy minus convention has an exact nonzero-form obstruction formula rather
than being silently reused. The corrected map is now extended to the current
linear matter, gauge-coordinate, internal-ghost and auxiliary sectors with
componentwise and product square-zero proofs and a bridge from
`IndependentFields`. The three rotations preserve the equatorial throat,
commute with deck, descend to the quotient and keep their `so(3)` bracket;
their scalar/Koszul action and the LL maps are explicit. The throat differential
is odd, Koszul-Leibniz and square-zero, making the LL completion unconditional;
the eight positive diagonal throat-metric magnitudes now carry an exact
log-coordinate ghost action, globally positive exponential curves and an odd
Leibniz square-zero BRST combined with LL. A first finite field/antifield
doublet and canonical pairing are closed; general spacetime metrics and the
full BV master equation remain.
It also has an automatic scalar integrability contract for every finite measure
on the affine-stable class with continuous fixed-frame covector components,
including arbitrary nonzero constant scalars; this is not a tensorial
continuity theorem. An intrinsic positive fixed-patch energy replacement is
uniformly equivalent to the implemented localized graph density and closes
uniform graph ellipticity without the variable-`chartAt` continuity contract;
identification with the historical raw holonomic density remains open. Its
independent variation also projects to the D9 slots
actually supplied by the diagonal package, while a literal finite D10
product-mode truncation uses the same period and exact PT-regulator pairing.
For the general tensor density, the subsequent frame-covariance gate closes
pointwise frame independence and true D8-diffeomorphism naturality; smooth
density packaging, finite-measure integrability, the global scalar action and
its derivative are then closed on the explicit regular sharp/frame/volume
field space. A global regular metric witness from the diagonal branch remains
open. The deck-compatible anti-periodic determinant now isolates why its
global frame cannot be the right witness. Canonical local tangent frames, a
smooth subordinate partition, a nonempty flat local regularization and local
musical/sharp/tensor/positive-volume data are constructed; exact tensorial
gluing is the remaining step.
The product cover nevertheless has a concrete nonempty Lorentz cocycle:
the tangent `S³` orthogonal plus the line direction carries a nondegenerate
`(3,1)` musical, and the actual deck reflection is an exact isometry. The
intrinsic dependent-tensor and quotient-descent bridges are now explicit
types, not assumptions hidden in the action.
For the same global holonomic scalar action, weak Euler `K` and symmetric
Jacobi `J` are defined for all smooth fields under the common integrability
contract and are exactly its first and second variations. The Lorentz time
coefficient is proved negative. Consequently only the explicitly time-static,
positive-mass sector is completed to a positive Hilbert energy space. Its
dense Riesz realization extends as a bounded self-adjoint bijection with
closed range and Fredholm index zero, and its pairing remains the Hessian of
the same action. No positivity of the full Lorentzian evolution or compact
resolvent is claimed.
The Robin chain now continues from the same action through its symmetric
Hessian to a self-adjoint index-zero `L²` Fredholm realization when
`k_+ + k_- != 0`; action, variation, Hessian and operator are PT-covariant
under sector/coupling exchange for a PT-invariant measure.
A separate geometric junction gate evaluates the genuine differential of the
same bulk scalar on a representative of the differential normal quotient.
The resulting covector has the required one-loop sign, pairs globally with a
twisted normal section, and yields an action and weak balance by stationarity.
The splitting is algebraic pointwise and the Robin identification remains an
explicit constitutive condition, not a derived unit-normal law.
A smooth section of the true D8 normal line fills the D9 normal slot locally,
with one-loop sign equal to the square of either constructed global `Z4` root
line. Real-linear complex conjugation now exchanges the two root-line descent
cocycles for every winding and is involutive. The rank-one normal principal
`Pin⁻(1)` lift is constructed; no ambient tangent Pin/SpinC principal bundle
or canonical global scalar normal coordinate is claimed.
Nonlinear diffeomorphism-BRST/SpinC/general-metric integration and the full
action--Hessian--domain identification remain explicit. The global LL action
also has its exact finite-measure measure/flux derivative and algebraic
zero-flux Euler branch. PT covariance is exact for fields, variations, action,
Euler coefficients and stationarity under PT-invariant measures. A second LL
functional on the same throat now contains true manifold derivatives through
a finite smooth tangent-generating frame and a strictly positive nonconstant
auxiliary-metric weight. Its integrated flux and auxiliary-metric derivatives
and exact weak stationary equation are proved. A strong divergence equation,
intrinsic Lorentzian contraction and boundary flux remain open. Averaging this
same differential functional with its PT pullback gives exact PT invariance of
the action, first variation, weak equation and stationary space for every
measure; the chosen generating frame itself is not made PT-equivariant. It
also has the exact symmetric PT-covariant flux Hessian of that same action,
equal to the linearization of its weak pairing, with positive kinetic part;
the raw auxiliary-metric Hessian is derived separately. Its weak Euler and
Jacobi maps are actual linear operators on smooth tests, with exact affine
linearization, Jacobi symmetry and same-action variation/Hessian identities;
in the strictly positive LL-measure sector this Hessian defines a completed
Hilbert energy space and its exact Riesz representative. The bounded
completion is self-adjoint, has zero kernel, full closed range and index zero,
and its smooth pairing is the same Euler linearization. No compact resolvent,
external Sobolev equivalence or D10 identification is claimed. It also supplies an exact
Frechet derivative of the full co-diagonal Candidate-A density through the
spectral covector and Sylvester inverse.  A two-dimensional Lorentz-boost orbit
also gives coordinate off-diagonal root/target derivatives and a Sylvester
identity, while remaining conjugate to its diagonal seed and reconstructing
the metric pair from the selected root; it is not a new geometric branch.  The
candidate also supplies an independent two-dimensional Lorentz-metric family
whose relative matrix is a non-diagonalizable Jordan block for nonzero
parameter, with an explicit square root, actual derivatives and a Sylvester
identity.  This is one family, not a global principal-root branch.  The
same null-coordinate construction is now embedded genuinely in dimension four
with two positive spatial directions; its root squares to the relative product
of two independently supplied symmetric metrics and the nonzero family is
proved non-diagonalizable. This is one 4D Jordan stratum, not a classification
or a globally glued branch. An explicit null frame certifies signature `(3,1)`
for both metrics throughout the family, and a finite bilateral inverse proves
Sylvester regularity and uniqueness of the root tangent even at non-diagonal
points. Algebraically, the whole similarity-invariant locus `(A-I)²=0` now has
the canonical root `I+(A-I)/2`, an exact bilateral Sylvester inverse and
continuous stratum restriction. It glues to the global positive-diagonalizable
selector on their exact intersection `{I}`; higher-index and non-unipotent
Jordan strata remain open. The same construction now extends to all
`(A-I)³=0` targets using `I+N/2-N²/8`, with a strict index-three witness,
bijective polynomial Sylvester inverse and exact extension of the index-two
selector. The final locus `(A-I)⁴=0` is now closed by the cubic truncation,
including a strict size-four witness, continuous restriction and polynomial
Sylvester inverse. This exhausts all unipotent `4×4` Jordan sizes; only
non-unipotent Jordan spectra remain. A rescaled gate now covers an arbitrary
single positive eigenvalue `λ>0`, with joint continuity, similar matrices,
exact square, bijective Sylvester and agreement at `λ=1`. Multiple-eigenvalue
spectra now include a closed positive `2+2` stratum with blockwise root,
similarity, continuity and finite-series Sylvester inverse. Positive `3+1` and
`2+1+1` are now closed identically. Every strictly-positive real Jordan
partition of dimension four is therefore covered from supplied presentation
data. One inductive sum now unifies all five partitions and proves exact square,
Sylvester bijectivity, continuity per stratum and combinatorial exhaustivity.
Deriving such presentations from raw spectral data and selecting the final
physical admissible domain remain. For raw matrices, split positive charpoly
now implies the needed minpoly facts and Jordan--Chevalley is exposed; Mathlib
has no Jordan-basis constructor. The entire residual is one named bridge
`PositiveRealJordanBasisBridge4`, after which square and Sylvester are already
closed. Root existence is already unconditional on the full PSD raw locus via
Mathlib `CFC.sqrt`, leaving only the split-positive non-PSD residual. For
nonpositive spectra, determinant negativity and a simple negative
diagonal eigenvalue are exact obstructions, while determinant positivity is
explicitly shown insufficient. Paired negative scalar and identical Jordan
blocks have constructive real roots. The complete negative-block parity and
zero-block criterion is stated, with its raw-matrix equivalence reduced to one
missing Jordan-classification bridge. Pure conjugate-complex pairs have an
exact real principal branch off the cut, an explicit cut closure, continuity,
zero singularity, `2+2` sums and a non-semisimple complex Jordan-chain root.
Only the raw charpoly-to-presentation bridge remains for that pure-nonreal
sector, but every raw relation `(A-aI)²=-b²I`, `b≠0`, already has an explicit
affine polynomial root. The Jordan bridge is equivalently reduced to its
necessity half and sufficiency outside the unconditional PSD/quadratic union. The
candidate further has a continuous three-parameter two-dimensional
null-coordinate Cayley--Hamilton root chart for independently supplied Lorentz
metrics, covering diagonalizable and Jordan points.  It proves neither
uniqueness nor a global or four-dimensional principal branch.  The candidate
now also supplies, on that chart, an explicit two-sided Sylvester inverse,
bijectivity and a unique solution for every target variation.  Differentiating
the square identity identifies any supplied differentiable explicit-chart
root curve's derivative with that inverse.  These are local two-dimensional
statements, not a global
four-dimensional root or Sylvester theorem.  The candidate
further supplies an exact finite-frame density weight
and an invariant finite-site weighted action under sitewise diagonal frames,
a genuine affine 1D pullback `J_epsilon rho(phi_epsilon)` whose variation is
the total derivative `(xi rho)'`, followed by a local affine `R^4` flow whose
actual Jacobian-determinant derivative and density pullback equal the
four-coordinate flux divergence, and a flat Minkowski linearized-Einstein
symbol with directly proved Bianchi contraction and gauge annihilation,
a typed gravitational boundary ledger with an actual local inverse-compatible
determinant-measure GHY curve, an actual
`K(t)=tr(h(t)^{-1}B(t))` derivative with no supplied `delta K`, a derived
Gaussian-normal Palatini/EH cancellation, and an explicit local embedded
hypersurface with two-sided surface inverse, Levi-Civita Christoffels, signed
unit normal and derived `B_ab` and `K`, followed by actual threefold interval
integration of the already-derived constant EH boundary-flux and GHY
first-variation densities on a compact tangent box, and an exact finite-box
Stokes theorem for arbitrary variable three-dimensional fluxes, all six
oriented faces and the cancelling counterterm.  Its bulk, boundary and matched
ledgers are actual derivatives along affine flux curves, and the matched
derivative vanishes. A further finite-stratified gate sums arbitrary weighted
Gaussian-normal non-null faces with their exact-inverse GHY curves, genuinely
integrates the reparametrization shift on oriented null generators, cancels
the endpoint joints, and proves the total finite residual is zero. These are
still quadrature/cellulation and one-dimensional-generator statements, not an
arbitrary-coordinate continuum GHY/null/joint theorem. It also supplies a
continuous but formally
non-differentiable zero-expansion
extension, null/joint endpoint transgression, pointwise LL auxiliary
metric/measure/flux variations with a conditional null-kernel branch, an
affine signed composite LL measure built from three auxiliary-scalar first
jets with actual line variations, coordinate compensation and a genuine
Frobenius-space Frechet derivative, Euclidean and explicit Minkowski Gram
`K/J` models with source/ambient naturality, exact infinitesimal kernels and
finite principal-symbol kernels, plus an exact arbitrary-nonzero-frequency
Lorentzian Gram--Saint-Venant symbol sequence by explicit pivot reconstruction,
now lifted coefficientwise to arbitrary finite families of nonzero Fourier
modes.  A separate finite gate uniquely decomposes every symmetric compatible
family into a normalized Gram image and a symmetric zero-frequency residual,
with an idempotent residual projection and the resulting finite cohomology
characterization.  Infinite-series convergence, PDE solvability and boundary
conditions remain open.  It also has an explicit matrix covector and
unconditional finite-frame commutator pairing,
actual spectral-plus-matter Euler/Hessian/Helmholtz equations and, separately,
an independent-coordinate scalar first-jet density with actual measure,
inverse-metric, scalar and gradient variations but no holonomic/determinant
relations or covariant PDE.  A finite periodic model now enforces the
holonomic gradient relation, proves the actual scalar-action derivative,
discrete summation by parts, the strong nearest-neighbour Euler equation and
stationarity equivalence; it is not a continuum covariant PDE or determinant-
measure result.  A positive one-dimensional metric version now induces
`sqrt(g)`, the inverse kinetic weight and the holonomic scalar variation from
the same metric and field variables.  This remains finite and periodic, not a
four-dimensional covariant scalar PDE or stress tensor.  Under every bijection
of finite site sets, its transported action is invariant, its first variation
and strong Euler field are equivariant, and fixed-metric stationarity is
preserved.  This remains finite reindexing, not a spacetime diffeomorphism.  It
also supplies an
exact reduced
Legendre/Dirac-chain bridge, a finite-site ultralocal mixed-primary functional
bracket equal to the sum of local secondaries with localized primary
preservation, followed by exact canonical Jacobi for arbitrary symmetric
nonlinear second jets and actual quadratic-bracket derivatives (neither is an
actual Candidate-A or continuum ADM closure), a PT-flat vacuum rank no-go and
a positive-dust constrained witness with independent rank and fixed lapse
ratio, a
one-dimensional constrained-tangent audit separating its negative ambient
Hessian from zero variation along an exact nonlinear constraint curve, a
relative-source rejection precursor, a reduced PT-signed source bridge with
positive Candidate-A matter Hessian, positive spin-2 kinetic form and the full
Newtonian sign table (with the charge law still supplied), and explicit Candidate-A
witnesses showing that the paired anomaly proxy fixes neither normalization
nor a reduced finite even-counterterm proxy, together with the actual
finite-mode heat-trace cancellation/even-doubling witness and a countable
cutoff limit with exact cancellation and a summable infinite-trace bridge,
then an explicit circle Fourier spectrum with Gaussian summability and
symmetric-cutoff convergence, together with its maximal-domain diagonal
operator proved dense, closed, unbounded and self-adjoint.  Its actual square
on Fourier basis vectors is now bridged to the existing finite and summable
diagonal traces.  A genuine bounded continuous diagonal heat operator is also
contractive, equals the identity at zero and satisfies the semigroup law.
Strong continuity is proved for every Hilbert-space state at every
nonnegative time, and each orbit in the dense Fourier basis has the expected
`-lambda_n^2` derivative. On the full Fourier Hilbert space, the maximal
strong right-generator domain is now exactly the squared spectral domain,
which is also the actual iterated domain of `D ∘ D`; the generator is `-D²`.
An independent contractive pure-point functional calculus on the proved
Fourier spectrum preserves unit, products and adjoints, and its scalar
function `x ↦ exp(-t x²)` is exactly the same heat operator. At every positive
time it is also an operator-norm-convergent sum
of explicit rank-one Fourier maps with summable norms, and the resulting
nuclear trace equals the spectral heat trace. No general Mathlib trace-class
interface or full Janus anomaly theorem is proved. For the normalized bounded
circle family, the actual determinant fibers now form a genuine complex
`FiberBundle`/`VectorBundle`, with a global interval trivialization, a
homeomorphic large-gauge clutching and descent to `AddCircle 1`. Its continuous
regularized determinant coordinate defines a section that vanishes exactly at
the endpoint crossings and is distinct from the everywhere-nonzero Fourier
frame. No Quillen metric, Bismut--Freed connection, curvature or global Janus
family index is obtained. See
`docs/program_p_explicit_covariant_candidate.md`.

The remaining package must lift these finite/pointwise results and close the
covariant source/boundary problem:

1. extend the co-diagonal root, its coordinate off-diagonal boost orbit, the
   independent non-diagonalizable Jordan witnesses, including the genuine 4D
   stratum, and the continuous
   three-parameter two-dimensional Cayley--Hamilton chart with its explicit
   bijective Sylvester inverse and derivative identity,
   together with the full interaction-density Frechet derivative, to a smooth
   unique real Lorentzian square-root branch for independently supplied
   four-dimensional metrics beyond the now-closed simultaneously diagonal
   global sector, and lift the selected densities and their finite
   weight law from pointwise matrices to metric functional derivatives on a
   manifold;
2. lift the finite-site frame model, the finite scalar reindexing covariance and
   the local affine four-dimensional pullback to the global Janus field space,
   independent variations and arbitrary diagonal diffeomorphism action;
3. lift the Gaussian-normal Palatini flux and explicit local embedded
   `h/B/K` chart to arbitrary coordinates and a global boundary curve, extend
   the finite variable-flux six-face Stokes result to continuum variable
   geometric data, choose an admissible
   zero-expansion
   variational domain, derive the geometric null/joint transformation laws,
   instantiate and integrate all slots, and lift the affine composite LL
   measure and pointwise auxiliary action to global fields, worldvolume PDEs
   and a nonempty throat branch;
4. lift the finite Gram-tensor map and no-double-counting chain rule to the
   chosen immersion/bulk geometry;
5. extend the finite zero-mode cohomology decomposition through infinite-series
   convergence and boundary analysis to the global Janus Lorentz compatibility
   differential/PDE complex;
6. lift the finite positive-metric periodic holonomic scalar variation, where
   measure and inverse already come from one metric, to a four-dimensional
   continuum matter field and stress tensor, then lift
   spectral Helmholtz and the reduced proxy audit to the
   nonlinear block Helmholtz and field-dependent Noether gates, derive the
   displayed reduced kinetic Lagrangian and dust source from the covariant
   action, lift the
   explicit dust-supported branch, derive the supplied reduced signed-charge
   law from the covariant Candidate-A weak-field equations, lift the local
   four-dimensional divergence and flat Einstein-symbol identities to the
   nonlinear curved covariant Bianchi identity, then extend the finite
   ultralocal primary bracket and nonlinear canonical second-jet Jacobi gate to
   the actual Candidate-A constraints and continuum ADM shift/spatial
   functional Poisson and hypersurface-deformation closure, with independent
   secondary-constraint closure and
   stability on the physical reduced tangent/quotient;
7. extend the self-adjoint unbounded circle Fourier operator to the full Janus
   Dirac operator, lift the now-closed circle generator/pure-point functional
   calculus comparison to that global operator, prove the required trace-class
   statements, compute variational
   cohomology, determinant data and actual regulated local/global anomalies,
   and close constrained stability in one scheme;
8. derive a microscopic normalization and finite-part law without
   observed-radius input.

## 13. Honest conclusion

Program P has substantially reduced the logical freedom, but it has not selected the physical Janus action.

The current gates now state exact acceptance tests for nonlinear cross-source
integrability, admissible boundary completion, induced-field variation and
diagonal gauge balance. Candidate A supplies explicit cross densities and an
exact spectral Euler model plus a separate independent-coordinate metric-
coupled scalar first-jet variation, a finite periodic holonomic scalar Euler
model, its positive one-dimensional metric/measure refinement, and nonlinear
canonical second-jet Jacobi. They cannot yet be applied in the general
tensorial sector until the full Lorentz field domain, metric/matter PDE
variations, global spacetime gauge generator and physical geometric boundary
functional are constructed.

The candidate point chart now passes an actual nonlinear Helmholtz test with
independent matter blocks. This does not discharge the covariant Janus PDE
Helmholtz, Bianchi, constraint or variational-cohomology obligations.

Likewise, the Jordan family and continuous two-dimensional Cayley--Hamilton
chart, including its bijective Sylvester inverse and derivative identity, do
not construct the unique global Lorentz root branch.  The
self-adjoint circle Dirac operator, its basiswise `D^2` trace bridge and the
strongly continuous contractive diagonal heat semigroup, including its exact
maximal `D²` generator domain, do not yet construct the full Janus Dirac
operator or a corresponding global functional calculus. On the circle, the
independent pure-point calculus now identifies its Gaussian exponential
exactly with the heat semigroup. Its
positive-time nuclear rank-one expansion supplies the concrete trace-class
property for the circle, but no global Janus trace-class family or anomaly is
computed, and it does not determine the global determinant or normalization.

What is established is a theorem/no-go architecture explaining exactly which
inputs are needed and which proposed shortcuts fail. The decisive missing
object is the global covariant realization of Candidate A, including its
admissible square-root domain, boundary/worldvolume problem, constrained Euler
system and one regulated microscopic normalization scheme.
