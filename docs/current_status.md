# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. It distinguishes compiled algebraic theorems, executable audits, conditional geometric interfaces and genuinely open Janus constructions.

## 1. Repository integration

The consolidated scientific stack was merged into `main` on 12 July 2026 through PR 5 at

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

Programs P-D and P-E were then advanced and merged into `main` through PR 6 on 14 July 2026 at

```text
92ade09c4f9aaab064840f934a42a50fb59bd171.
```

The merged PR 6 stack contains:

- the corrected finite-jet operator category and holonomic composition;
- invariant pairing modules and isotropy-stratification counterexamples;
- an action-groupoid core and exact orbitwise descent;
- concrete immersion and abelian-connection jet quotients;
- the universal low-order quotient represented by `(B,F)`;
- pointwise and smooth local adapted tangent/normal frames;
- the connection-corrected identity `B = II` and residual equivariance;
- moving-frame laws, normal transport and overlap Čech cocycles;
- oriented reduction to `SO(T) x SO(N)`;
- central Spin-lift and determinant-root defects with SpinC diagonal cancellation;
- concrete circle, matrix `SO(2)` and Mathlib Clifford `Spin(2)` models;
- the first Gauss--Codazzi--Bianchi algebraic identities;
- exact Codazzi and abelian Bianchi jet quotients;
- direct-product splittings of `nabla II` and abelian connection second jets;
- the algebraic normal Ricci equation;
- finite-dimensional Fréchet--Riesz construction of the shape operators from `II`;
- canonical pointwise and smooth normal-frame transitions;
- transition-jet bridges from frame derivatives to normal gauge extraction;
- a direct construction of the normal-frame transition derivative.

Program P-E was advanced again and merged into `main` through PR 10 on
15 July 2026 at

```text
96e60eb4df1db049f8488858c5a6b1fdb717b224.
```

## 2. Validation

The current `main` head is

```text
96e60eb4df1db049f8488858c5a6b1fdb717b224.
```

The theorem commits below the PR 6 merge were validated by its focused Lean
and Python workflows. The PR 10 theorem head was validated locally before
merge; this document does not claim an independent post-merge CI run for
`96e60eb4`.

The previously recorded successful runs include:

```text
Program PE jet universality       run 29268187119   Lean/Python success
Programs D and P integration      run 29268187102   all listed jobs success
Janus deep alpha completion       run 29268187105   Lean/Python success
```

PR 6 extends focused validation to include:

```text
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameTransitionJetBridge
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameTransitionDirectConstruction
```

Supported focused Lean heads include:

```text
JanusFormal.Branches.FundamentalGeometryD
JanusFormal.Branches.FundamentalGeometryDiracSpectral
JanusFormal.Branches.FundamentalGeometryD7SpectralTheory
JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation
JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz
```

A green Lean head means that every imported theorem and proof compiles. It does **not** turn uninstantiated status fields into geometric objects or prove the complete physical Janus theory.

### PR 10 merged update (15 July 2026)

The PR 10 theorem head, now merged into `main`, was validated locally with

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

The integrated head compiles. Independent post-merge remote CI is not claimed
here. New proved, scoped constructions are:

- existence of the smooth finite-dimensional Euclidean Levi-Civita/Koszul
  coefficient from a smooth positive-definite metric;
- a projected-seed atlas for the varying intrinsic normal spaces, with smooth
  orthogonal overlap maps and coefficient transition laws;
- the canonical one-chart rank-two Clifford SpinC Cech bundle with the supplied
  smooth abelian potential as connection data;
- a valid-chart low-order residual/SpinC action groupoid extracted from actual
  Euclidean immersion, metric-Koszul and gauge-potential derivatives.

These do not assert the full differentiable Janus jet groupoid or a nontrivial
global Janus SpinC bundle.

The current follow-on branch also proves that two actual valid projected-seed
chart extractions at the same base point are related by the canonical residual
normal-frame action, packages that relation as an action-groupoid arrow and
proves its identity and Cech composition laws. For invariant observables it
also constructs the unique chart-independent value at that fixed base point.
If the observable admits a smooth realization on the normed continuous-jet
coefficients, the descended observable is globally smooth by fixed-chart local
gluing. This remains low-order Euclidean descent, not effective descent for the
full Janus structured-jet groupoid.

The same branch supplies two conditional multi-chart packages. Given an open
cover, oriented cocycles, chosen Spin lifts, phase transitions and matching
diagonal defects, Lean packages the resulting SpinC transitions with pointwise
identity, inverse and Cech laws. This is a supplied transition presentation,
not a continuity/smoothness theorem or a geometric principal-bundle total-space
construction. Given local abelian potentials and additive overlap shifts, Lean
proves the affine first-jet law and, when every overlap shift is curvature-flat,
uniquely glues the local curvatures to a global smooth curvature function. Its
actual Fréchet derivative satisfies the cyclic abelian Bianchi identity. These
packages do not
derive their input from actual Janus characteristic classes, determinant-line
transitions or logarithms, and therefore do not construct the global physical
Janus SpinC bundle or connection.

## 3. Stable architecture

```text
D0/D8  mapping-torus and one-sided-throat topology
D2/D7  twisted Dirac, eta, heat-kernel and determinant constraints
D9     gauge-fixed elliptic-symbol and BRST/ghost gates
D10    determinant-line, Quillen and anomaly interfaces
D11    natural-operator and finite-jet gates

P0     moduli-geometry no-go
P-A    relative action specification / parent-bulk reduction
P-B    anomaly consistency and discrete selection
P-C    Helmholtz inverse variational problem
P-D    isotropy-stratified pairing and invariant-coefficient modules
P-E    structured jets, adapted frames, SpinC lifts and integrability
P-F    compatibility pullbacks, Helmholtz and Noether identities

A/B/C  quantum scale, nonlinear junction and charge compatibility
E      observational falsification after theoretical closure
```

## 4. Topology and Z4

For

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translated action is treated as a free smooth mapping-torus action. The expected fundamental group is `Z`, not `Z4`.

Quarter phases arise conditionally by lifting the sign holonomy of a real normal line:

```text
one real-normal loop       -1
square-root multipliers    +i or -i
two lifted loops           -1
four lifted loops          +1
```

Thus `Z4` is a lift/holonomy phenomenon. A square-root or `Z4` lift is additional global data, not a canonical functor of the underlying line bundle.

## 5. Program P

### P0, P-A, P-B and P-C

- **P0:** a metric does not select a potential; a symplectic form does not select a Hamiltonian.
- **P-A:** the two-sector parent-bulk result now extends to an arbitrary finite boundary rank: the bulk Euler expression is the actual derivative, the reduced action has the Schur gradient and constant Hessian as its Fréchet derivatives, and exact square completion classifies the fixed-boundary stationary bulk mode as the unique global minimum/maximum according to the sign of the bulk coefficient; the Schur kernel is reciprocal/self-adjoint, while changing the parent can still change surviving mixing. In the concrete one-dimensional positive PT-flat proportional bimetric branch, the reduced interaction has its actual derivative, `c = 1` is stationary, its actual Hessian is twelve times the Fierz--Pauli mass combination, and for `beta1 > 0`, `beta2 >= 0` it is positive and `c = 1` is the unique global minimizer on `c > 0`; this is not the full Janus metric field theory.
  More strongly, explicit quadratic and quartically deformed two-variable
  extensions have the same proportional branch, the same genuine longitudinal
  derivatives and the same complete transverse two-jet, with Hessian
  `2 kappa`, all along that branch. A nonzero `lambda * y^4` term still makes
  them distinct off the branch, so even the local transverse Hessian does not
  select the nonlinear extension. This is a reduced reconstruction no-go, not
  a full metric action.
- **P-B:** four explicit finite candidates realize every anomaly/Helmholtz truth pattern, so anomaly cancellation is an independent consistency filter rather than a dynamics principle.
- **P-C:** finite quadratic and polynomial Helmholtz reconstruction is formalized, including the exact three-sector PT-plus-reciprocity criterion. For the finite quadratic Euler family, self-adjointness of the actual Jacobian is equivalent to the coefficient Helmholtz swaps; these data construct a normalized cubic polynomial primitive with the prescribed actual Fréchet derivative, and derivative equality alone recovers its formal coefficients. A Poincaré--Helmholtz theorem reconstructs an action from a symmetric differentiable Euler one-form on an open convex configuration domain; on the whole space, under a global actual-gradient hypothesis, additive linear gauge invariance is equivalent to Euler horizontality. More generally, for a supplied complete differentiable one-parameter flow, full-orbit invariance is equivalent to annihilation of its field-dependent generator by the actual Euler derivative; horizontal Helmholtz data give an invariant normalized radial primitive. No Janus flow, gauge group or PDE identity is constructed; the nonlinear Janus Euler family, Noether system and variational cohomology remain open.
  The set quotient by complete-flow orbits is constructed. For any target,
  functions on this quotient are equivalent to configuration-space functions
  invariant under the flow; the real-valued specialization gives the same
  equivalence for actions, including the radial action. No topology or smooth
  structure is put on this quotient, and the supplied flow is not a concrete
  Janus flow.

### P-D — pairings and coefficient modules

Formalized/audited:

- `Z4` and PT selection rules;
- low-rank scalar, vector, tensor and spinor pairing dimensions;
- multiplicity-space freedom for repeated sectors;
- closure under invariant scalar coefficients;
- failure of pointwise multiplicity one to imply one constant global coupling;
- jumps of invariant-fiber dimensions across isotropy strata.

The correct global object is an equivariant pairing module over the invariant scalar algebra, not only a pointwise Hom-space.

### P-E — structured jets

#### 5.1 Categorical and groupoid core

The current `main` stack proves, in the declared models:

- local finite-jet factorization under the stated Peetre--Slovak hypotheses;
- naturality/equivariance and evaluator uniqueness;
- holonomic composition;
- action-groupoid, orbit and stabilizer laws;
- reconstruction of equivariant sections on one transitive orbit from isotropy-fixed values;
- a concrete valid-chart low-order residual/SpinC action-groupoid realization;
- the need for separate compatibility across isotropy strata.

The operator category is not an ordinary category of fixed linear representations with plain fiber maps.

#### 5.2 Low-order quotient

For an adapted immersion two-jet, the chain rule gives

```text
Q_tangent -> Q_tangent + C
Q_normal  -> Q_normal.
```

The source orbit is classified by the normal tensor. Abelian connection one-jet gauge orbits are classified by curvature. The combined quotient is `(B,F)` and has the universal invariant-factorization property.

#### 5.3 Adapted geometry and `B = II`

Lean constructs:

- tangent image and orthogonal normal complement;
- coordinates with `di(x)=(x,0)`;
- smooth tangent/normal projectors;
- smooth local adapted orthonormal frames by projected Gram--Schmidt;
- the connection-corrected second derivative;
- the flat-adapted identity `B=II`;
- residual `O(T) x O(N)` equivariance;
- moving-frame corrections, normal transport and overlap Čech laws;
- determinant-one reduction to `SO(T) x SO(N)`;
- canonical pointwise normal-frame transitions;
- smooth adjoint-formula transitions on overlaps;
- transition jets and their direct derivative construction.
- a projected-seed varying-normal atlas with smooth transition and coefficient laws;
- constructive smooth Euclidean metric-Koszul connection existence.

These constructions package a genuine projected-seed normal atlas, but not yet
the complete global Janus frame/normal bundle over the full background space.

#### 5.4 SpinC and rank-two Clifford model

Lean proves:

- central `±1` lift defects;
- two-torsion determinant-root defects;
- diagonal SpinC cancellation when the defects match;
- the circle-squaring cover and kernel `{±1}`;
- `U(1) ≃ SO(2)`;
- equivalence with Mathlib's even-unitary Lipschitz `CliffordAlgebra.spinGroup` for the negative Euclidean plane;
- the Clifford-valued rank-two central double cover and SpinC diagonal quotient;
- the canonical one-chart Cech principal bundle and a connection from the
  supplied global smooth gauge potential;
- conditional multi-chart SpinC Cech transition packaging from supplied
  pointwise cocycles, lifts, phases and matching defects, without transition
  continuity/smoothness or a principal-bundle total-space construction;
- conditional abelian connection overlap descent from supplied local
  potentials and additive gauge shifts, with unique global smooth curvature
  descent under the flat-shift condition and a cyclic Bianchi identity for its
  actual Fréchet derivative.

Higher-dimensional Clifford covers, derivation of the supplied cocycles from
actual Janus bundles, nontrivial/global Janus principal-bundle construction,
determinant-line identification and characteristic-class matching remain open.

#### 5.5 Codazzi and abelian Bianchi exactness

The current `main` stack proves:

- Gauss curvature symmetries from symmetric `II`;
- Codazzi and abelian Bianchi skew/cyclic identities;
- exact classification of Codazzi fibers by fully symmetric third-order corrections;
- exact classification of connection second-jet fibers by symmetric gauge third jets;
- canonical `1/3` sections and universal quotient properties;
- exact splittings

```text
j1(II)  ≃  Sym3(T*) tensor N  x  ClosedCodazzi,
j2(A)   ≃  GaugeJet3_sym       x  Closed(nabla F).
```

The Codazzi tensor is only the quotient component of `nabla II`; the fully symmetric third-order component remains independent data.

#### 5.6 Normal Ricci equation and Riesz shape operators

The algebraic Ricci stage starts from

```text
<A_xi x,y> = <II(x,y),xi>.
```

Lean proves self-adjointness of `A_xi` and the tangent/normal antisymmetries of

```text
<[A_xi,A_eta]x,y>.
```

The current `main` stack goes further: for a symmetric bilinear finite-dimensional `II`, it constructs `A_xi` by Fréchet--Riesz representation. Finite-dimensional bilinear continuity is supplied automatically by Mathlib. The Weingarten relation, self-adjointness, commutator symmetries and the algebraic Ricci reconstruction therefore follow from `II`, rather than from independently assumed shape operators.

Still open:

- identify the proved projected-seed/fixed-model family with the actual global
  Janus `II` bundle over the full structured-jet base;
- insert the genuine ambient mixed curvature and normal-connection curvature;
- prove the manifold-level Ricci equation.

### P-F — compatibility pullback

A self-adjoint target Hessian pulls back to a self-adjoint quadratic Helmholtz
operator; gauge invariance gives the linearized Noether identity. The abstract
compatibility-complex synthesis now packages `K R = 0`, `B K = 0`, pulled-back
self-adjointness, gauge-Hessian degeneracy and restricted Helmholtz in one
theorem. It assumes the algebraic complex and pairing; the actual nonlinear
second-variation chain rule is also proved in normed spaces as
`H(Ju)(Jv) + dL(D²K(u,v))`, reducing to `H(Ju)(Jv)` when the target gradient
`dL` vanishes. Schwarz symmetry makes this complete second variation symmetric
even off criticality and therefore makes the critical `J^T H J` symmetric
without a separate symmetry postulate for `H`. At a target critical point the
pullback is genuinely critical, and its actual Hessian annihilates `ker J` in
either slot; hence it annihilates `im R` when `J ∘ R = 0`. These are abstract
Fréchet statements. For every source submodule contained in `ker J`, this
critical Hessian descends uniquely and symmetrically to the algebraic module
quotient. Continuity of the descended form and any normed, topological or
smooth quotient structure are not proved. No concrete Janus compatibility map
or complex is constructed; the global variational primitive remains open.

## 6. Current supported chain

```text
actual decorated Janus data
  -> regular local finite-jet presentation
  -> structured action groupoid and holonomic operator category
  -> low-order quotient (II,F)
  -> smooth local adapted frames and oriented overlap cocycle
  -> canonical normal-frame transition jets and gauge extraction
  -> Spin/determinant defects and rank-two Clifford SpinC model
  -> first Gauss--Codazzi--Bianchi quotient stages
  -> split data: Sym3 + Codazzi and gauge3 + nabla F
  -> Riesz shape operators from II
  -> algebraic normal Ricci equation
  -> actual ambient/normal/determinant connection jets
  -> higher structured jet-isomorphism theorem
  -> stratified invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether + anomaly consistency
  -> action class, microscopic normalization and effective potential
  -> stable vacuum and absolute scale
```

The repository does **not** yet contain the full differentiable Janus structured-jet groupoid, a global Janus SpinC principal bundle, the geometric higher-order jet-isomorphism theorem, the concrete nonlinear Janus Euler family, a selected microscopic action, a unique vacuum or an absolute no-fit scale.
