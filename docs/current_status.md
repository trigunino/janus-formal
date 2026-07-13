# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. It distinguishes compiled algebraic theorems, executable audits, conditional geometric interfaces and genuinely open Janus constructions.

## 1. Repository integration status

The consolidated scientific stack was merged into `main` on 12 July 2026 through PR 5 at commit

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

Draft PR 6 advances Programs P-D and P-E on branch

```text
agent/categorical-jets-and-pairing-modules.
```

It now contains:

- the corrected category of natural finite-order jet operators;
- invariant pairing modules and isotropy-stratification counterexamples;
- an action-groupoid core and exact orbitwise descent;
- concrete immersion and abelian-connection jet quotients;
- the universal low-order quotient represented by `(B,F)`;
- pointwise and smooth local adapted tangent/normal frames;
- the connection-corrected identity `B = II` and residual equivariance;
- moving-frame two-jet laws, normal transport and overlap Čech cocycles;
- oriented reduction to `SO(T) x SO(N)`;
- central Spin-lift and determinant-root defects with SpinC diagonal cancellation;
- concrete circle, matrix `SO(2)` and Mathlib Clifford `Spin(2)` models;
- the first Gauss--Codazzi--Bianchi algebraic identities;
- exact Codazzi and abelian Bianchi jet quotients;
- direct-product splittings of `nabla II` and abelian connection second jets;
- the algebraic normal Ricci equation through commutators of shape operators.

Until PR 6 is merged, none of these additions should be attributed to `main`.

## 2. Validation truth

The latest theorem head is

```text
2825863c67e45630af445979a78a05ab11541dae.
```

It was validated by **Program PE jet universality**, run `29266824488`:

```text
Lean build of FundamentalGeometryPEJetUniversality   success
P-E executable audits                               success
focused Python tests                                success
```

The corresponding **Programs D and P integration matrix**, run `29266823478`, completed successfully across all listed Lean and Python jobs. **Janus deep alpha completion**, run `29266823577`, also completed successfully.

### Supported focused Lean heads

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

A green Lean head means that every imported theorem statement and proof compiles. It does **not** turn uninstantiated fields of a status structure into geometric objects, and it does not establish the complete physical Janus theory.

## 3. Stable scientific architecture

```text
D0/D8  global mapping-torus and one-sided-throat topology
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

## 4. Topology and Z4 verdict

For the candidate

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translated action is treated as a free smooth mapping-torus action, not as a reflection orbifold with a local singular fixed stratum. The expected fundamental group is `Z`, not `Z4`.

The quarter phases arise conditionally from lifting the sign holonomy of a real normal line:

```text
one real-normal loop       -1
square-root multipliers    +i or -i
two lifted loops           -1
four lifted loops          +1
```

Thus `Z4` is a lift/holonomy phenomenon. A square-root line or `Z4` lift is additional global data and is not a canonical functor of the underlying line bundle.

## 5. Program P — precise position

### P0 — moduli-geometry no-go

**Formalized:** a metric does not select a potential; a symplectic form does not select a Hamiltonian; a Kähler-like package still requires a moment map or functional.

### P-A — relative action selection

**Formalized:** a quadratic Hessian fixes an action only up to an affine functional. A Hessian, critical point and reference value determine a normalized quadratic action. A quadratic parent-bulk problem yields a Schur-complement boundary action.

**Open:** select and derive the actual Janus parent action and boundary data.

### P-B — anomaly filter

**Formalized in finite proxies:** PT pairing cancels the parity-odd contribution. Anomaly cancellation is independent of parity-even Helmholtz integrability and does not determine all even couplings or finite counterterms.

### P-C — Helmholtz reconstruction

**Formalized:** finite quadratic Hessian realizability is equivalent to formal self-adjointness; finite polynomial Helmholtz conditions reconstruct a cubic potential.

**Open:** derive the nonlinear Janus Euler source, Noether identities, nonlinear Helmholtz conditions, variational cohomology and boundary/null terms.

### P-D — invariant pairings and coefficient modules

**Formalized/audited:**

- `Z4` neutrality and PT selection rules;
- low-rank scalar, vector, tensor and spinor pairing dimensions;
- multiplicity-space freedom for repeated sectors;
- closure under invariant scalar coefficient functions;
- a counterexample showing that pointwise multiplicity one does not imply one constant global coupling;
- a counterexample showing that invariant-fiber dimensions can jump across isotropy strata.

The correct global object is an equivariant pairing module over the invariant scalar algebra, not only a pointwise Hom-space.

### P-E — structured jets and geometric reduction

#### 5.1 Categorical and groupoid core

The repository proves, in the declared abstract models:

- local finite-jet factorization under the stated Peetre--Slovak hypotheses;
- naturality/equivariance and uniqueness of jet evaluators;
- holonomic composition of finite-order operators;
- action-groupoid identity, composition, inverse, orbit and stabilizer laws;
- exact reconstruction of equivariant sections on one transitive orbit from isotropy-fixed values;
- the need for separate compatibility across different isotropy strata.

The category is not an ordinary category of fixed linear representations with plain fiber maps. Its morphisms use jet prolongations and holonomic composition.

#### 5.2 Low-order source and gauge quotient

For a first-order-normalized immersion two-jet, Lean derives from the second-order chain rule

```text
Q_tangent -> Q_tangent + C
Q_normal  -> Q_normal.
```

The source orbit is classified exactly by the normal quadratic tensor. For a local abelian connection one-jet, gauge orbits are classified exactly by curvature.

The combined low-order quotient has reduced data

```text
(B,F),
```

and satisfies a universal property: an observable is invariant under the source/gauge orbit directions exactly when it factors uniquely through `(B,F)`.

#### 5.3 Adapted geometry and the second fundamental form

Lean constructs:

- the tangent image and orthogonal normal complement of an isometric derivative;
- adapted coordinates in which `di(x) = (x,0)`;
- smooth tangent and normal projectors;
- smooth local adapted orthonormal frames by projected Gram--Schmidt;
- the connection-corrected second derivative;
- the exact flat-adapted identity `B = II`;
- residual `O(T) x O(N)` equivariance;
- moving-frame correction laws and canonical normal transport;
- identity, inverse and Čech laws for adapted-frame overlaps;
- determinant-one reduction to `SO(T) x SO(N)`.

These are local and algebraic/smooth-coordinate theorems. They have not yet been packaged as the complete global Janus frame and normal bundles.

#### 5.4 SpinC defect and rank-two Clifford model

Lean proves:

- the central `±1` defect of chosen lifts through a double cover;
- the two-torsion triple defect of local determinant-line square roots;
- diagonal cancellation in `(Spin x U(1))/⟨(-1,-1)⟩` when the defects match;
- the circle-squaring double cover `z -> z^2`, its kernel `{±1}` and two-sheeted fibers;
- an explicit group equivalence `U(1) ≃ SO(2)`;
- an equivalence between the circle model and Mathlib's even-unitary Lipschitz `CliffordAlgebra.spinGroup` for the negative Euclidean plane;
- the resulting Clifford-valued central double-cover package and rank-two SpinC diagonal quotient.

Still open are the higher-dimensional Clifford Spin covers required by the actual tangent and normal dimensions, smooth principal-bundle packaging, and characteristic-class matching for the Janus data.

#### 5.5 First integrability and Spencer stages

The repository now proves:

- algebraic Gauss curvature symmetries generated from a symmetric second fundamental form;
- the Codazzi skew/cyclic identities;
- the abelian Bianchi skew/cyclic identities;
- exact classification of Codazzi-jet fibers by fully symmetric third-order corrections;
- exact classification of abelian connection second-jet fibers by symmetric gauge third jets;
- canonical one-third sections for the closed Codazzi and closed `nabla F` targets;
- universal quotient properties for invariant observables;
- exact direct-product splittings

```text
j1(II)  ≃  Sym3(T*) tensor N  x  ClosedCodazzi,
j2(A)   ≃  GaugeJet3_sym       x  Closed(nabla F).
```

The first equality means that the Codazzi tensor is only the quotient component of `nabla II`; the fully symmetric third-order component remains independent reduced data unless another symmetry removes it.

#### 5.6 Algebraic normal Ricci equation

Given the Weingarten relation

```text
<A_xi x,y> = <II(x,y),xi>,
```

Lean proves that every shape operator is self-adjoint. Therefore

```text
<[A_xi,A_eta]x,y>
```

is skew both in `x,y` and in `xi,eta`. Adding this term to the ambient mixed-curvature component produces an algebraic normal-curvature tensor satisfying the pointwise Ricci equation by construction.

This is not yet the curvature of the genuine Janus normal connection. The finite-dimensional Riesz construction of `A_xi`, insertion of actual ambient mixed curvature and actual normal-connection curvature remain geometric obligations.

### P-F — compatibility pullback

**Formalized:** a self-adjoint target Hessian pulls back through a compatibility-map linearization to a self-adjoint quadratic Helmholtz operator; gauge invariance gives the linearized Noether identity.

**Open:** construct the actual Janus compatibility complex, target pairing and global variational primitive.

## 6. Current supported chain

```text
actual decorated Janus data
  -> regular local finite-jet presentation
  -> structured action groupoid and holonomic operator category
  -> low-order quotient (II,F)
  -> smooth local adapted frames and oriented overlap cocycle
  -> Spin/determinant defects and rank-two Clifford SpinC model
  -> first Gauss--Codazzi--Bianchi quotient stages
  -> split data: Sym3 + Codazzi and gauge3 + nabla F
  -> algebraic normal Ricci equation
  -> actual ambient/normal/determinant connection jets
  -> higher structured jet-isomorphism theorem
  -> stratified invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether + anomaly consistency
  -> action class, microscopic normalization and effective potential
  -> stable vacuum and absolute scale
```

The repository does **not** yet contain the full differentiable Janus structured-jet groupoid, a global Janus SpinC principal bundle, a higher-order geometric jet-isomorphism theorem, the concrete nonlinear Janus Euler family, a selected microscopic action, a unique vacuum or an absolute no-fit scale.

## 7. Immediate theorem queue

1. Construct shape operators from `II` by finite-dimensional Riesz representation and connect them to the existing algebraic Ricci theorem.
2. Insert the curvature of an actual normal connection and the ambient mixed-curvature tensor; prove the geometric Ricci equation.
3. Prove residual `O(T) x O(N)` equivariance and smooth jet-bundle compatibility of the Codazzi, `nabla F` and Ricci stages.
4. Identify the reduced abelian curvature and its derivatives with those of the SpinC determinant-line connection.
5. Construct the higher-dimensional Clifford Spin covers needed by the tangent and normal ranks.
6. Package local frames, transitions and lifts into global oriented and SpinC principal bundles.
7. Prove characteristic-class matching of the Spin and determinant-root defects for actual Janus data.
8. Add ambient curvature jets and derive the complete Gauss--Codazzi--Ricci--Bianchi realizability conditions.
9. Extend the exact Spencer splittings by one order and identify the first genuine higher-order obstruction.
10. Construct the differentiable structured-jet groupoid and effective descent for tensor, spinor, twist and ghost sectors.
11. Classify orbit types and smooth extension across higher-isotropy strata.
12. Under explicit compact/reductive and polynomial/weight hypotheses, prove finite generation of invariant and equivariant modules.
13. Insert the resulting operator basis into the nonlinear Helmholtz/Noether system.

## 8. Navigation

- [`PROGRAM.md`](../PROGRAM.md) — stable program map;
- [`program_master_roadmap.md`](program_master_roadmap.md) — detailed dependency graph;
- [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md) — corrected operator category;
- [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md) — structured-jet reduction program;
- [`program_pe_low_order_structured_background.md`](program_pe_low_order_structured_background.md) — concrete `(B,F)` quotient;
- [`program_pe_spinC_cocycle_lift.md`](program_pe_spinC_cocycle_lift.md) — SpinC defect and lift program;
- [`program_pd_global_pairing_modules.md`](program_pd_global_pairing_modules.md) — pointwise-to-global pairing correction;
- [`janus_branch_registry.md`](janus_branch_registry.md) — supported heads and gate-only collections.
