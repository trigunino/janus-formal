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
quotient. The effective deck groupoid has exactly one isotropy stratum with
trivial stabilizers, and every supplied structured-jet representation sends
its endomorphisms to identities. Its regular-object stratum is all objects,
its singular stratum is empty, and dependent sections restrict/extend through
this stratification by mutually inverse maps with unique extension. This does
not yet construct the physical
SpinC representation or classify its fiber isotropy, higher jets or a
Peetre--Slovák integrability theorem.
Independently, the fixed quotient itself now forms a one-object symmetry
category with every smooth D8 self-diffeomorphism as an arrow. The period is
also promoted to object data in a larger category of all nonzero-period
effective D8 quotients, with genuine smooth cross-background diffeomorphisms
and an exact contravariant constant-fiber smooth-field functor. Its actual
tangent bundles are transported by manifold derivatives and its cotangent
fibers by exact contravariant dual pullback. Covariant rank-two tensor fibers
inherit the exact composition law, their symmetric subspaces are preserved and
their smooth sections form a global contravariant functor. Musical
equivalences and Lorentz inertia `(3,1)` are transported as well, giving a
global functor of smooth general Lorentz metrics. This effective family is not
yet the decorated moduli category of all Janus backgrounds or its principal
SpinC/Pin bundles.

At the ambient `Pin⁻(4)` level, every certified continuous Čech lift of the
actual reduced atlas now produces a genuine principal fiber-bundle core on the
real quotient, with exact cocycle and free/transitive right action. The
remaining issue is existence of that ambient lift, not principal-bundle
assembly once it is supplied.

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
an open nonzero complement, transported exactly by this diffeomorphism. Any
continuous intrinsic quadratic form on this normal line now gives the exact
spacelike/timelike/null/non-null partition and closed joint frontier, with
fiber-scaling invariance. For the restricted spacetime metric, the construction
is reduced to one local projection lemma in the transported normal charts:
preservation of quotient classes, metric orthogonality and continuity of the
squared length. This lemma is now explicit on every canonical chart chosen by
a cover lift: the pushed latitude normal gives a nonzero quotient class and
scalar fiber coordinates, while its orthogonal representative has exact
scalar-square metric value and a continuous local quadratic model. Change-of-
lift/deck compatibility is now exact at tangent level for every winding and
supplies a chosen anchor-independent global fiber-linear orthogonal lift that
represents the quotient class. Its metric square is globally continuous under
`CanonicalGlobalNormalMetricSquareLocalRegularity`; that local contract and a
dependent continuous lift record remain open. Under the same contract, the
square directly defines the global spacelike, timelike, null, non-null and
joint strata and proves their open/closed laws, total cover and joint-in-null
inclusion without constructing that record. The actual latitude tangent on
the throat cover is now explicit and its raw ambient derivative is `(e₀, 0)`.
The sphere ambient map and its smoothness are public, and the intrinsic ambient
derivative is exactly factored through the public product-coordinate
derivative, including pointwise evaluation. The product derivative is now the
continuous-linear equivalence induced by the global product diffeomorphism;
the canonical latitude normal has exact ambient image `(e₀, 0)`, and both that
image and the tangent vector are nonzero. For the actual intrinsic cover
Lorentz tensor, its square is exactly `1` and it is orthogonal to every tangent
in the fixed-throat differential, hence spacelike and non-null. Its quotient
pushforward realizes the canonical local lift above. The resulting local
orthogonal decomposition proves `HasNoTangentialRadical` for the retained
intrinsic Lorentz metric, hence a genuinely nondegenerate smooth throat trace
packaged on the nondegenerate metric domain. Under one deck turn the quotient
latitude curve reverses its parameter, the tangent normal obeys the exact
dependent sign law, and the `-id` clutching preserves both the scalar-square
model and the metric square of the local orthogonal lift. Continuous global
gluing of those local lifts remains open. The named cover latitude normal is
now explicitly `HEq` to the raw derivative of its curve after transport along
the zero-latitude equality. The quotient projection chain rule now transports
this identity to an `HEq` between the pushed canonical quotient normal and the
quotient-latitude tangent. An explicit zero-latitude base transport turns this
bridge into equality in one tangent fiber and is proved to commute with scalar
multiplication. The pushed canonical normal therefore satisfies the exact
normal-sign cocycle for every integer winding and induces the global algebraic
lift above. The unconditional local regularity proof and dependent continuous
packaging remain open.
The actual quotient charts also give the real ambient tangent transitions,
their invertible differentials, nonzero determinants and exact orientation
parity cocycle. An explicit positive nondegenerate model form is now transported by
each tangent transition with a genuine quadratic isometry. Choosing one actual
reference lift at every quotient point and transporting through the true
tangent cocycle now constructs an atlas-wide pointwise orthonormal reduction.
An independent Whitney pullback construction now inhabits its `C∞` refinement:
the metric application, Gram--Schmidt frame application and orthogonal overlap
application are jointly smooth on the genuine chart domains. The Clifford
`spinGroup` now supplies a true
quadratic-preserving vector action and morphism `Spin(Q) →* GL(4)`, with the
twisted Pin extension isolated exactly. Atlas-specific transition lifts,
their Čech cocycle, comparison with the normal lift and SpinC remain open. The
reference `Pin⁻` generator now projects to the explicit last-coordinate
reflection, with determinant `-1`, and its full `ZMod 4` orientation character
is proved. The corrected overlap-level frontier reduces the ambient lift to
the actual Čech winding, its normal comparison and one exact `O(4)` reduction
law. The canonical winding is now constructed from the genuine ambient local
sections. The fixed-throat inclusion is natural on an explicit open chart
refinement, and on the resulting compatible overlap the ambient winding is
exactly `localTransitionWinding`. This does not identify the sign of the true
ambient Jacobian, whose chart orientations remain visible. The smooth
orthonormal refinement is closed; determinant-parity comparison, the exact
`O(4)` reduction law and ambient `Pin⁻` lift remain open. The determinant
comparison now has an exact no-go without additional chart data: composing
one chart with the reference reflection preserves the winding while toggling
the Jacobian parity. Hence a compatible orientation gauge is a genuine input,
not a consequence of the deck cocycle. Likewise, the central frame change
`-id` preserves the orthonormal metric but changes the exact `O(4)` transition,
so a frame gauge must also be fixed before imposing the reference matrix law.
Pointwise this gauge exists uniquely as `actual⁻¹ ∘ expected`; the remaining
algebraic compatibility is exactly its proved conjugation-twisted Čech law,
with a proved converse. A smooth atlas-wide, normal-compatible realization
remains open.
The corresponding vertex-frame formula is also closed: it preserves the
strict Čech law, gives the exact conjugated edge gauge, and uniquely propagates
a source gauge from a fixed target gauge. Constructing one globally smooth
propagation with the prescribed normal restriction remains open.
An explicit root-chart propagation realizes the complete target cocycle on
every star subatlas. Global path independence, smoothness and the normal
boundary prescription remain open.
Loop closure is characterized exactly by conjugacy of actual and target
holonomies through the root gauge; this genuine-atlas criterion is not yet
discharged.
Because the mapping-torus holonomy is cyclic, intertwining its generator is
proved sufficient for every integer winding. What remains is the genuine
atlas-level identification of that actual generator.
For any orthogonal frame aligning the geometric normal with the reference
axis, this generator identification and all-winding closure are now exact.
Constructing such an aligned frame smoothly on the genuine atlas remains open.
Pointwise, such a frame now exists for every unit normal by an explicit
Hilbert-reflection construction transported back to the ambient quadratic
coordinates. Its smooth atlas-wide selection remains open.
Moreover, quaternionic left multiplication upgrades this to a canonical
jointly `C∞` frame formula for every smooth unit-normal field, without a pole
singularity. Instantiation with the genuine normalized atlas normal and its
overlap laws remains open.
Normalization is also closed: every smooth nonzero normal field normalizes
smoothly and feeds the jointly smooth quaternionic frame. The residual task is
to identify and regularize the genuine atlas-coordinate normal field.
Its signed overlap behavior is already exact: reversing the local normal
reverses the normalized normal and multiplies the quaternionic frame by the
central `-id` gauge, consistently with the nontrivial normal line.
The statement holds for all integer windings via the genuine normal sign
representation, not only for one loop.
The conjugated aligned reflection is invariant under that central frame sign,
so it descends across the one-sided normal cocycle even though the frame does
not.
This sign-independent reflection is packaged for every nonzero local normal
and descends for the complete integer winding character.
At the Clifford level, every unit normal now defines a genuine ambient
`Pin⁻(4)` generator. Normal reversal multiplies it by the nontrivial central
sign, while its orthogonal projection is unchanged; after normalization this
gives the exact lift and projection laws for every integer winding. The open
step is its instantiation on the genuine atlas normal and comparison with the
actual reduced transitions.
For each such local normal, the full integer lift `w ↦ g(n)^w` satisfies the
strict cyclic cocycle and projects to the matching power of the local
reflection.
That projected reflection is proved exactly equal to the quaternionic aligned
reflection, including all integer powers, via the explicit Clifford rank-one
formula.
The actual canonical latitude normal on the throat cover now supplies a
nonzero product-coordinate representative, so this cyclic ambient `Pin⁻`
lift and its aligned projection are instantiated on the genuine cover
geometry. Atlas-overlap descent remains the next step.
For independent overlap and phase windings, the lift transforms by exactly the
corresponding power of the central Pin sign; this is the required local gauge
law before inserting the actual atlas transition functions.
Changing the genuine throat-cover anchor by any integer winding preserves the raw product
normal and every local cyclic lift; the normal reversal is therefore not
hidden in the representative and must occur in the quotient transition.
On the actual throat chart domains, evaluating at the local covering sections
and using `localTransitionWinding` gives normalized ambient `Pin⁻(4)` lifts
with a strict triple-overlap Cech cocycle and the exact aligned projection.
The full ambient-atlas transition comparison and continuity remain open.
For every normed real coefficient fiber, smooth deck-invariant fields on the
analytic cover now descend `C∞` and are exactly equivalent to smooth fields on
this quotient; the flat two-metric/two-scalar/root witness consequently lives
on the actual smooth spacetime. PT pullback and two-sector exchange are exact
involutive equivalences on these smooth coefficient fields. Smooth quotient and throat fields now carry genuine real vector-space structures. The actual compact quotient sends every smooth coefficient field canonically into the completed `L²` space for any finite Borel measure; completeness and the Hilbert structure follow under the explicit complete/Hilbert fiber hypotheses. For a PT-preserving measure, PT pullback is an involutive linear isometry and hence an exact `L²` equivalence. Smooth restriction to the actual throat is defined, linear, PT-equivariant, and yields a nonempty exact PT-compatible Dirichlet subspace. A finite global `C∞` tangent-generating family feeds a complete first-jet graph `H¹` space with dense smooth fields and continuous `L²` forgetting. For throat-supported spacetime measure, its continuous trace has norm bound one. For the canonical physical volumes, the exact FTC/Fubini estimate, twisted analytic latitude collar, throat pushforward and `L²` trace identity are proved. The normal derivative is exactly reconstructed by the finite global frame with an explicit pointwise coefficient bound. Joint `C∞` latitude regularity closes tangent-lift continuity and compact reconstruction; the exact radial--polar cone calculation closes physical coarea. The canonical physical trace bound, operator, smooth agreement and existence theorem are unconditional. Only identification with an intrinsic Sobolev trace space remains open.
The positive collar is explicitly homeomorphic and measurably equivalent to
the band `x₀ ∈ Ioc(0,sin 1)` in `S³`. Its weighted pushforward is reduced
by `Measure.toSphere_apply'` to
`CanonicalPositiveLatitudeEuclideanConeJacobianFormula`, an ordinary 4D cone
volume identity. The identity is proved directly by the volume-preserving
`ℝ⁴ ≃ ℝ³ × ℝ` split, Mathlib's spherical radial and planar polar formulas,
and the exact radial factor `∫₀¹ r³ dr = 1/4`. The reciprocal-cosine,
product/time, quotient, Fubini/map, coarea and final trace chain is therefore
closed without an extra chart certificate. Joint `C∞` latitude regularity also
makes compact normal-frame reconstruction unconditional.
The kernel of the resulting physical trace is now a closed, complete and
nonempty homogeneous Dirichlet graph-`H¹` space. Membership is exactly zero
physical trace and agrees with zero canonical `L²` trace on smooth fields.
A canonical nested `ℓ²`/`WithLp 2` renorming now closes the same smooth jets in
a genuine Hilbert space. Its lifted fiberwise norm equivalence maps that
closure exactly onto the original graph completion and gives a continuous
linear equivalence agreeing on smooth fields. The transported physical trace
has a closed Hilbert Dirichlet kernel, a contractive orthogonal projection and
an exact orthogonal splitting, and this kernel is continuously linearly
equivalent to the original graph-Dirichlet kernel. No intrinsic Sobolev
identification is inferred.
The independent-field PT/exchange theorem now uses a unified packet whose two
metric slots are arbitrary `SmoothGeneralLorentzMetric` fields and whose
matter, gauge, ghost, auxiliary and LL/throat slots are unchanged. It is an
exact involution; all retained non-metric smooth throat data intertwine the
trace and preserve Dirichlet conditions. Each metric now restricts through
the actual throat inclusion to a smooth symmetric covariant two-tensor, and
the boundary packet contains both traces. The trace is nondegenerate exactly
when the ambient metric has no tangential radical along the throat. Metric
restriction now commutes pointwise with intrinsic PT tensor pullback, and the
two traces obey the exact PT/exchange law. Because the throat PT derivative is
a linear equivalence, the pointwise pullback preserves and reflects
nondegeneracy and `HasNoTangentialRadical` is invariant under PT and
PT/exchange. A smooth intrinsic PT-pullback section for an arbitrary throat
tensor and classification of general metric restrictions remain open. A
pointwise PT/exchange matching relation on two
smooth metric boundary references avoids assuming that missing pullback; it
is functional, preserves nondegeneracy, is satisfied by actual ambient metric
traces, and transports the full metric/non-metric Dirichlet equality.
For the retained intrinsic metric, time-reversal naturality of the cover
immersion derivative is now public and proves exact cover isometry. Naturality
of quotient projection derivatives and uniqueness of tensor descent then make
the complete metric/musical and the equal two-sector pair genuine PT fixed
points; the intrinsic throat trace is fixed and remains nondegenerate.
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
functional derivative under an explicit domination contract. This is a genuine curved-base diagonal field functional, not yet a general tensorial action. Intrinsic smooth symmetric covariant two-tensors and their nondegenerate Lorentzian `(3,1)` fiber domains are now defined, and symmetry, nondegeneracy and signature are preserved by fiber pullback. For the actual analytic PT map, the raw tensor pullback and two-sector exchange are exact involutions; local tangent/Hom coordinates now discharge `AnalyticPTTensorPullbackLocalSmoothness` unconditionally, so the dependent pullback is an involutive smooth tensor section preserving the smooth Lorentz domain. The exact musical equivalence now follows the same pullback, producing an involutive PT action and sector exchange on `SmoothGeneralLorentzMetric`; the holonomic scalar density is pointwise PT-covariant for the transported field and frame. Integrated spacetime invariance and BV remain separate. Refining such a metric by its exact musical equivalence now gives the same-tensor inverse contraction, Gram determinant volume, genuine `p=d phi` scalar density and exact pointwise quadratic variation; frame independence, smooth density and integration remain open. On that same quotient, one global independent-field package now contains the two positive diagonal metrics, two matter multiplets, gauge-coordinate pairs, ghosts, auxiliaries, and throat/LL coefficient fields. Metric matrices, the principal root, and matter traces are uniquely induced rather than independently varied. Their simultaneous componentwise variation chain is now exact, including zero induced cross-response from gauge, ghost, auxiliary and LL directions. The abelian `U(1)^2` gauge coordinates are promoted to intrinsic smooth one-forms; `A ↦ A+dλ`, pullback naturality, BRST `s(A,c)=(dc,0)`, nilpotence and the bridge to both independent ghosts are exact. A separate genuine smooth tangent ghost now has exact pullback laws, scalar Lie derivative and a nilpotent linearized BRST complex connected to the independent matter field. Nonlinear graded diffeomorphism BRST, metric Lie derivatives and BV remain open. A finite global `C∞` tangent-generating family closes the frame input of the graph-`H¹` construction; for throat-supported spacetime measure its trace has exact norm bound `1`, while the canonical physical-volume trace bound/operator/existence theorem are unconditional and only intrinsic Sobolev identification remains open. A global smooth scalar also carries its genuine manifold differential `p = d phi`, with exact throat and PT chain rules. Its fixed-frame diagonal action contracts this differential with the inverse of the same metric, uses that metric's exact volume density, and has exact pointwise and integrated scalar variation at fixed metric/measure under an explicit integrability contract; the covariant Euler--flux equation remains open. A quadratic Robin action built from the actual throat restrictions now yields an exact integrated weak two-sector flux balance and vanishing squared residual at stationary points; geometric normal derivatives and Israel/null junction conditions remain open. Arbitrary smooth diagonal self-diffeomorphisms of the actual spacetime/throat pair now act contravariantly on every independent coefficient sector, preserve positivity, obey the exact identity/composition/inverse laws and commute with smooth throat restriction whenever they preserve the inclusion. A supplied smooth orbit has a genuine manifold tangent generator at time zero. The LL measure/flux coefficients define an actual integrable worldvolume action on the compact throat for every finite Borel measure, and the PT-matched zero configuration is a nonempty zero-action branch. The null counterterm is differentiated on the explicit open admissible domain `Theta ≠ 0`; zero remains excluded by the proved non-differentiability. The candidate
The integrated-invariance limitation just stated is now superseded: coherent
PT transport of a `SmoothGeneralLorentzMetric`, scalar and tangent family
gives exact density covariance, iff integrability transport and invariance of
the action against the canonical quotient Lorentz measure. The tangent family
is still supplied explicitly and this measure is not identified with every
general metric's own volume. At fixed metric, the affine scalar line has an
exact pointwise/integrated quadratic expansion and action derivative under the
explicit three-coefficient integrability contract; its first variation is
PT-covariant pointwise and after integration, with iff integrability transport.
For an arbitrary smooth D8 self-diffeomorphism, simultaneous transport of the
metric, scalar, tangent family and inverse-pushforward measure gives exact
pointwise covariance, iff integrability, integrated action invariance and the
direct two-sector exchange corollary. Tangent/Hom-bundle coordinates construct
the smooth tensor pullback for every such diffeomorphism, while the genuine
derivative transports the musical equivalence and Lorentz inertia; hence the
metric-pullback certificate is unconditional. On a supplied smooth orbit,
the action orbit is exactly constant and has zero derivative; the explicit
non-vacuous first-variation contract identifies this derivative with the scalar
diffeomorphism Noether pairing.
The jointly analytic D8 time action additionally yields its genuine smooth
tangent ghost and the proof that it is the velocity of the complete flow.
Restricting to this real direction and the existing `U(1)^2` parameters gives
the combined metric--matter--gauge `R/B` block and its infinitesimal Noether
identity. The metric-derivative smoothness/symmetry input remains an explicit
specialized contract; this does not integrate arbitrary tangent ghosts and
does not add LL.
Separately, the actual metric gradient `sharp(dφ)` and an exact
divergence/boundary-flux interface now turn the
general first variation into the weak covariant Euler pairing plus flux.
Zero flux gives the stationarity equivalence, and the construction is
specialized to the intrinsic D8 metric. The intrinsic contravariant scalar
stress is additionally pointwise covariant under every smooth D8
diffeomorphism after coherent transport of the metric, `dφ` and cotangent
tests. Its measured pairing with arbitrary cotangent test fields transports
integrability iff and is invariant under diffeomorphism plus sector exchange.
These pointwise, measured, two-sector and integrated-variation laws are now
packaged by one unconditional scalar-stress covariance/exchange certificate;
that covariance certificate alone makes no conservation claim. A separate
covariant scalar second-jet calculation in a four-dimensional normal frame
now proves the exact local identity
`∇_μ T^{μν} = (□φ - V'(φ)) sharp(dφ)^ν` and its vanishing under the Euler
residual. It recovers both existing potential conventions: `V' = -m²φ` for
the intrinsic-fiber stress and `V' = m²φ + source` for the matrix stress. A
pointwise metric-compatible torsion-free connection jet now transports this
identity to arbitrary coordinates: the covariant Hessian is symmetric and an
explicit `∂T + ΓT + ΓT` realization cancels to the normal representative,
again giving Euler conservation. The connection-jet interface is now
discharged pointwise from a symmetric nondegenerate metric and a
metric-symmetric first jet: the local Levi-Civita formula is torsion-free,
obeys covariant and inverse-metric compatibility, and uses the exact identity
`∂g⁻¹ = -g⁻¹(∂g)g⁻¹`. For every supplied smooth holonomic quotient patch, the
genuine `SmoothGeneralLorentzMetric` now yields a smooth nondegenerate local
metric, inverse, `fderiv` metric jet and Christoffel coefficients. Every
genuine smooth quotient scalar pulls back to a `C∞` coordinate representative.
Its gradient and raw Hessian are `C∞`, define a coordinate scalar jet and obey
Schwarz symmetry. The resulting covariant jet, Euler residual, raised gradient
and canonically realized local stress divergence are also `C∞`, with exact
identity `div T = EulerResidual · raisedGradient`; Euler conservation follows
at every patch coordinate. For supplied overlap representatives, equality of
the metric first jet and scalar second jet now implies equality of the local
Christoffels, covariant jet, Euler residual, raised gradient and divergence.
Generic patch construction, the real chart-transition theorem producing those
jet equalities and pointwise gluing are now closed: componentwise total-ball
maps construct a genuine holonomic patch through every quotient point, hence a
field-independent covering atlas. Scalar Euler equations therefore imply
chartwise and quotient-pointwise zero local stress divergence. This does not
construct a second abstract global covariant-derivative field.
The concrete throat flux `trace(ψ) · dφ(n)` equals its metric-gradient form and
vanishes pointwise and integrally for homogeneous Dirichlet variations. On the
canonical latitude collar, genuine interval-integral IPP identifies the
normal `mvfderiv` term and removes the boundary for endpoint-Dirichlet tests.
The intrinsic metric-gradient pairing with the explicit collar normal is now
proved equal to that derivative, so the oriented two-endpoint flux defines an
exact collar divergence/boundary interface. Its weak Euler plus boundary
decomposition, measured flux and Dirichlet stationarity are concrete. A
predicate and adapter record when a supplied global interface specializes to
this collar result; they do not prove global Stokes or construct a global
one-sided normal.
The associated scalar Green--Wronskian current is antisymmetric, its derivative
is exactly the antisymmetric pairing of the two equal-mass Euler residuals,
and it is pointwise and measured constant for two Euler solutions. Its endpoint
jump is the antisymmetrized concrete IPP boundary functional, while homogeneous
Dirichlet Euler pairs make it vanish. The Wronskian is now realized as a
genuine tangent current along the quotient collar, carried by the intrinsic
unit-spacelike canonical normal. Its metric normal flux is exactly the Green
current, is locally conserved for equal-mass Euler pairs, and at the throat is
the concrete pairing of their normal `mvfderiv`s. The autonomous collar
equation also has
the exact energy `(φ')² + m²φ²`, whose derivative is `2φ'` times the Euler
residual. It is therefore fiberwise and measured constant on Euler solutions,
has zero endpoint jump, and is nonnegative for `m² ≥ 0`. This is a local
one-dimensional stress-energy witness. More precisely, the metric dual of the
intrinsic unit normal identifies this energy exactly with twice the
normal-normal component of the general scalar stress on the normal-projected
collar jet; that component has zero derivative and is locally constant under
the collar Euler equation. This is not a four-dimensional covariant stress
divergence theorem for smooth fields. A global geometric Stokes theorem identifying the abstract
bulk boundary functional with this collar flux, a global canonical metric
normal, and extension to a covariant four-dimensional Noether current with
enough test ghosts remain open.
The candidate now has a genuine `ZMod 2` exterior coefficient algebra on three odd
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
doublet and canonical pairing are closed. Its finite CE reduction is now a
genuine `32`-dimensional BV master model with canonical odd Darboux
antibracket, nonzero even action `S(q,p)=p(dq)`, exact classical master
equation `(S,S)=0`, Hamiltonian generation of the square-zero BRST vector
field and an exact embedding back into the throat doublet. This model is now
promoted fibrewise to smooth fields on the actual throat, with smooth
square-zero BRST/master density, pointwise CME, canonical integrated action
and an explicit nonzero witness. Exact affine first variation, its
gradient/BRST identity, the odd antibracket on represented analytic ultralocal
functionals and the integrated CME are closed. The canonical throat measure is
now proved PT-preserved from its round-`S²` × signed-period pushforward, making
the integrated master action, first variation, represented value, odd bracket
and CME PT covariance unconditional. This does not extend the construction
beyond represented ultralocal throat functionals. Separately, the same fixed
`32`-dimensional BV fibre is now promoted to smooth fields over the actual D8
spacetime quotient, with smooth square-zero BRST, throat restriction,
canonical-volume nonzero action and pointwise/integrated CME. The round-`S³`
reflection together with `t ↦ period-t` preserves the canonical quotient
measure, making the spacetime PT involution, BRST compatibility, integrated
master action and CME covariance unconditional. Its exact affine first
variation, integrated directional derivative and odd antibracket/CME on
represented analytic ultralocal spacetime functionals are closed too. Their
exact fibre PT laws and integrated first-variation, represented-value,
odd-bracket and CME covariance are now unconditional as well. The same phase
is now coupled faithfully to the actual smooth strictly-positive diagonal
metric cone through its eight global logarithms, with metric ghosts,
antifields, corrected square-zero BRST, nonzero action, pointwise/integrated
CME and exact PT covariance. Derivative-dependent terms, completed spaces and
arbitrary BV functionals for general non-diagonal Lorentz tensors remain open;
a rank-one nonlocal model is closed below. The safe first tensorial level is nevertheless explicit: two
smooth symmetric general-metric variations and their antifields form a
nontrivial odd square-zero doublet, with background-raised trace pairing and a
graded-skew pointwise Darboux antibracket attached to the independent packet.
Analytic PT pullback with sector exchange is now an involution on this level,
commutes with its BRST differential and makes both the raised pairing and odd
bracket pointwise covariant. On the bulk itself, the genuine background metrics
now define the general-tensor ultralocal Hamiltonian `1/2 ⟨h⁺,h⁺⟩`. Its affine
polarization is exact, its actual `HasDerivAt` is the declared antifield-gradient
pairing, it generates `(h⁺,0)`, has an intrinsic action-`4` nonzero witness, is
PT/exchange covariant and satisfies the pointwise CME. Local tangent/cotangent
trivializations, smooth inversion of the finite-dimensional musical matrix and
trace invariance prove every smooth bulk pairing density continuous and `L¹`.
Thus action/bracket integrability and the integrated affine
`HasDerivAt`/gradient are unconditional; PT covariance and the represented CME
remain exact. Certified bulk functional observables now have actual gradients
and a functional odd bracket. Their rank-one nonlocal master
`1/2 (∫⟨K,h⁺⟩)²` has an exact affine derivative, functional CME, generated
square-zero BRST and an intrinsic nonzero witness. Derivative-dependent
kernels, completed spaces and arbitrary functionals remain open.
The actual throat inclusion now restricts every
  variation/antifield tensor smoothly. The induced boundary BRST remains
  square-zero and commutes with trace; PT/exchange matching is functional and
  transports the full metric-BV Dirichlet packet. The packet-level pointwise
  odd bracket keeps its PT/exchange covariance. On the retained PT-fixed
  nondegenerate intrinsic throat metric, the musical map now has a genuine
  pointwise inverse. It raises the traced variations/antifields and defines an
  intrinsic symmetric pairing and graded-skew odd bracket, with exact
  bulk-gradient-trace expansion and PT/sector-exchange covariance. The
  pairing is bilinear. The ultralocal pointwise action
  `S∂ = 1/2 ⟨h⁺,h⁺⟩` has an exact quadratic expansion on every affine smooth
  throat-antifield line, and its actual `HasDerivAt` is the pairing with the
  declared `antifieldGradient`. The intrinsic metric in both sectors supplies
  an explicit action-`3` nonzero witness. The action generates `(h⁺,0)`, is
  PT/exchange covariant and satisfies the pointwise CME. The inverse-pairing
  density is now proved globally continuous by local tangent/cotangent
  trivializations, continuous inversion of the finite-dimensional musical map
  and trace invariance. The continuity contract and every required `L¹`
  obligation are therefore discharged: the canonical-volume action and
  represented odd bracket are unconditionally integrable, their PT/exchange
  covariance is exact, the quadratic line formula gives a true unconditional
  `HasDerivAt` equal to the integrated `antifieldGradient` pairing, and the
  represented integrated CME holds. The analogous certified throat functional
  observables and odd bracket give a rank-one nonlocal master with exact
  derivative, functional CME, generated square-zero BRST and a nonzero
  intrinsic throat witness. Derivative-dependent kernels, completed spaces,
  arbitrary functionals, arbitrary general-throat inverse/classification and
  Lorentzian preservation of affine variations remain open.
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
A nonempty scoped common-domain package now makes the same independent
configuration feed the induced metrics/root, `LLH1`, its exact boundary trace
and typed D7/D9/D10 accessors. Agreement with the action tangent, Hessian,
full D10 diagonalization, regulator and Fredholm/boundary domains remains one
explicit residual contract. It now requires concrete linear/isometric modal
coordinates, density, action derivatives, Hessian spectral pairing and exact
domain equalities, with no unconstrained readiness propositions.
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
or canonical global scalar normal coordinate is claimed. The genuine smooth
tangent diffeomorphism ghost now fills the same local D9 package. A canonical
real rank-four coordinate equivalence fills its matter slot in the D11
squared-spinor coordinate specialization, closing that residual record only
at coefficient level, not as a geometric SpinC bundle. Independently, six
local symmetric metric coefficients project surjectively onto the full D9
metric slot at fixed non-metric data; these pointwise coefficients are not a
tangent to the global Program-P action. For a supplied smooth symmetric global
tensor, the total atlas now selects a compatible holonomic chart automatically
at every true throat point; its six `ContDiff` chart coefficients reproduce the
D9 metric slot exactly. This bridge still does not produce a global Program-P
action tangent. Nonlinear diffeomorphism-BRST, global
SpinC/general-metric integration and the full action--Hessian--domain
identification remain explicit. The global LL action
also has its exact finite-measure measure/flux derivative and algebraic
zero-flux Euler branch. PT covariance is exact for fields, variations, action,
Euler coefficients and stationarity under PT-invariant measures. A second LL
functional on the same throat now contains true manifold derivatives through
a finite smooth tangent-generating frame and a strictly positive nonconstant
auxiliary-metric weight. Its integrated flux and auxiliary-metric derivatives
and exact weak stationary equation are proved. The canonical throat volume is
now unconditionally positive on every nonempty open set, hence has full
support. A frame-divergence strong Euler field and the weak/strong and
stationary/strong equivalences are proved under the explicit analytic
realization, global integration-by-parts and zero-boundary-flux contracts.
The three canonical sphere rotations together with quotient-time translation
now give a smooth spanning frame whose flows preserve the canonical measure.
Their field derivatives integrate by parts unconditionally; after the exact PT
change of variables this proves the weighted global IPP and realizes the empty
boundary ledger for that canonical frame. This does not yet prove geometric
Stokes for arbitrary variable stratified data, an intrinsic Lorentzian
contraction or the complete covariant LL parent action. The raw operator's exact formal-adjoint
defect is now represented by an explicit correction interface: under a smooth
representative, weak solutions are exactly solutions of the corrected strong
equation, and the correction is zero exactly under global IPP. For the retained
canonical frame that IPP is proved, so its correction is exactly zero; the
interface remains conditional only for other frames. Averaging this
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
points. On the full real-diagonalizable strictly-positive locus, the continuous
presentation-independent selector now packages the local IFT atlas into a
unique continuous exact-square global lift agreeing with every presented local
branch. This statement does not cover Jordan strata, nonpositive spectra or
the general physical admissible domain. Algebraically, the whole
similarity-invariant locus `(A-I)²=0` now has
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
closed. This bridge is now constructed on the complete Hermitian
split-positive sector by the spectral-theorem unitary eigenbasis, including
all `PosDef` matrices. On the non-Hermitian complement, its only remaining
input is `PositiveRealNonHermitianJordanChainBasisResidual4`: an invertible
real chain-vector matrix, its intertwining identity and a partition of
`Fin 4`. The inverse, unified presentation, exact root and Sylvester regularity
are proved from that datum; only construction of the chain basis remains.
Root existence is unconditional on the full PSD raw locus via Mathlib
`CFC.sqrt` and now also on a strict non-PSD raw locus: the positive quadratic
relation `(A-λI)(A-μI)=0` has the exact affine root
`(A+√λ√μ I)/(√λ+√μ)`, including a repeated size-two Jordan block. The precise
raw result now covers every positive single-eigenvalue relation
`(A-λI)^4=0` through the exact third-order Taylor root. A strict size-four
Jordan witness is non-Hermitian, non-PSD and outside the quadratic locus. The
first genuinely multivalue Hermite locus is now also unconditional: for
distinct positive `λ,μ`, the relation `(A-λI)²(A-μI)²=0` has an explicit
cubic matching both values and derivatives of `sqrt`. Its degree bound,
divisibility by the squared annihilator and minpoly, and `q(A)²=A` are proved.
The canonical Jordan `2+2` witness is non-Hermitian, non-PSD and outside both
earlier algebraic loci. The distinct positive `3+1` relation
`(A-λI)³(A-μI)=0` is also closed by a cubic matching the order-two jet of
`sqrt` at `λ` and its value at `μ`. Three residual jets, cubic-times-linear
divisibility, the minpoly congruence and `q(A)²=A` are proved. Its canonical
Jordan witness lies outside PSD, quadratic, single-eigenvalue quartic and
double-double loci. Hermite interpolation now also closes `2+1+1`, while a
four-node Lagrange cubic closes `1+1+1+1`; both give the degree bound,
annihilator/minpoly divisibility and exact square. From an arbitrary
`PositiveRealSplitCharpoly4`, splitting and degree four extract four positive
roots with multiplicity, Cayley--Hamilton supplies their annihilator, and an
exhaustive equality partition reduces to one of the five constructive
profiles. Raw square-root existence is therefore unconditional on the full
split-positive locus. The non-Hermitian Jordan-chain presentation remains
separate only when an explicit normal form is required; a basis-free
polynomial-centralizer argument makes Sylvester regularity unconditional.
At the zero frontier, the canonical family `J₂(t) ⊕ 1 ⊕ 1` has an exact
Hermite root whose `1/(2√t)` coefficient and Frobenius norm diverge, with no
finite continuation, while its `E₀₁` Sylvester eigenvalue `2√t` collapses.
The same obstruction is proved for every fixed real similarity class. The
double collision `J₂(t) ⊕ J₂(s)` has two independent collapsing Sylvester
modes and no finite extension at the two-parameter zero corner. A genuinely
moving polynomial shear `P(t)=I+tE₂₀` now has an exact inverse, transported
root and mode, nonconstant target, divergent root coefficient and no finite
continuation. The singular diagonal scaling `P(t)=diag(t,1,1,1)` instead
regularizes the canonical divergence to a finite nonzero nilpotent root limit;
its inverse blows up and the Sylvester mode still degenerates. Two explicit
Jordan-type-change paths are now closed as well: `I+tE₀₁ → I` has the exact
smooth affine root `I+(t/2)E₀₁` while its Sylvester eigenvalue stays `2`, whereas
`t(I+E₀₁) → 0` has a root and Sylvester eigenvalue both tending to zero.
The diagonal, canonical, fixed-similarity, moving-shear, double-collision,
singular-frame and type-change witnesses are assembled in one proof-carrying
retained frontier certificate.
At one diagonal `0/0` boundary point, an equal-rate path and a
quadratic-numerator path reach the same limit while the selected root
coordinate tends respectively to `1` and `0`. Hence no continuous
single-valued extension can agree with the positive branch on the interior.
This is a two-path obstruction only, not a classification of general matrix
paths or Jordan strata.
The full positive monomial family `(t^m,t^n)`, `m,n>0`, is classified as well:
the root tends to `1` for equal exponents, to `0` when the numerator vanishes
faster, and to `+∞` when the denominator vanishes faster. Arbitrary nonlinear,
matrix-valued and Jordan-degenerate paths are not covered.
Arbitrary singular frames, a general Jordan-type classification/branch atlas
and arbitrary matrix `0/0` paths remain.
For
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
necessity half and sufficiency outside the unconditional
PSD/quadratic/single-eigenvalue-quartic/double-double/`3+1` union. The
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
the endpoint joints, and proves the total finite residual is zero.  The finite
null-face action is now assembled explicitly from the integrated inaffinity,
the continuously extended expansion counterterm and the endpoint joints.
Under `k -> exp(sigma) k` and the inverse parameter-measure weight, its two
face densities acquire exactly the proved local transgression; the full
action is invariant face by face and after every finite sum.  Its value and
finite scaling law remain valid at `Theta = 0`, while classical expansion
variation is correctly restricted to `Theta != 0`.  The ambient geometry must
still supply the area, generators and `NullFaceIntervalIntegrability`. These are
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
ratio.  That witness now lies in an explicit affine family whose nonvanishing
`3 x 3` constraint-minor parameter locus is open and nonempty; independence of
the three constraint covectors holds throughout that locus and eventually
around the witness.  This is not a generic phase-space rank theorem, an
ADM/covariant derivation or a Boulware--Deser exclusion.  A
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
