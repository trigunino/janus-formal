# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. Detailed derivations remain in the program-specific documents; this file states what is integrated, what is validated and what remains open.

## 1. Repository integration status

The consolidated scientific stack was merged into `main` on 12 July 2026 through PR 5 at commit

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

Draft PR 6 advances Programs P-D/P-E beyond that baseline. It contains:

- the corrected categorical jet statement;
- invariant pairing modules and isotropy-stratification locks;
- action-groupoid and orbitwise-descent cores;
- the first concrete low-order structured-jet quotient `(B,F)`;
- pointwise and smooth local adapted tangent/normal frames;
- the connection-corrected identity `B = II` and residual equivariance;
- the varying-frame second-jet law and canonical normal transport;
- Čech cocycles for adapted-frame overlap transitions;
- determinant-one reduction to `SO(T) x SO(N)`;
- central double-cover lift defects and abstract SpinC diagonal cancellation;
- determinant-line square-root defects and their `±1` circle realization;
- a concrete rank-two circle-squaring double cover;
- an explicit group equivalence `U(1) ≃ SO(2)` and matrix-valued two-sheeted Spin projection.

Until PR 6 is merged, these additions belong to branch

```text
agent/categorical-jets-and-pairing-modules
```

rather than to `main`.

## 2. Validation truth

The consolidated `main` workflows are green. On PR 6, the focused head

```text
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

builds successfully with the moving-frame, oriented-cocycle, SpinC defect and rank-two matrix layers imported.

The latest theorem code was validated at commit

```text
1995bb68d5c06a1c627732f24ed27883c576ff36
```

by workflow **Program PE jet universality**, run `29249977153`:

```text
Lean build                    success
P-E executable audits        success
focused Python tests         success
```

### Green focused Lean heads

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

D9 and D11 remain gate collections without supported standalone entry files.

A green Lean head means that its imported statements compile. It does **not** mean that every proposition stored in an abstract status structure has been realized by a concrete geometric or physical construction.

## 3. Stable scientific architecture

```text
D0/D8  global mapping-torus and one-sided-throat topology
D2/D7  twisted Dirac, eta, heat kernel and determinant constraints
D9     gauge-fixed elliptic-symbol and BRST/ghost gate collection
D10    determinant-line, Quillen and anomaly interfaces
D11    natural-operator and finite-jet gate collection

P0     moduli-geometry no-go
P-A    relative action specification / parent-bulk reduction
P-B    anomaly consistency and discrete selection
P-C    Helmholtz inverse variational problem
P-D    isotropy-stratified pairings and invariant-coefficient modules
P-E    finite jets, reduction, adapted frames and SpinC lift data
P-F    compatibility-map pullbacks, Helmholtz and Noether identities

A/B/C  quantum scale, nonlinear junction and charge compatibility
E      observational falsification after theoretical closure
```

## 4. Topology and Z4 verdict

For the candidate

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translated action is treated as a free smooth mapping-torus action, not as a reflection orbifold with a local singular fixed stratum. The equatorial throat target is `S2 x S1` and is one-sided in the nonorientable quotient.

The expected fundamental group is `Z`, not `Z4`. The quarter phases arise conditionally as a lift of the normal-line sign holonomy:

```text
one loop on the real normal line:       -1
complex square-root multipliers:        +i or -i
two lifted loops:                       -1
four lifted loops:                      +1
```

Thus `Z4` is a holonomy/lift phenomenon. A square-root line or `Z4` lift is extra global data; it is not a canonical functor of the underlying line bundle.

## 5. Program P — precise position

### P0 — moduli-geometry no-go

**Formalized:** a metric does not select a potential; a symplectic form does not select a Hamiltonian; a Kähler-like package still requires a moment map or functional.

### P-A — relative action selection

**Formalized:** a quadratic Hessian fixes an action only up to an affine functional. Hessian + critical point + reference value determine a normalized quadratic action. A quadratic parent-bulk problem yields a Schur-complement boundary action.

**Open:** select the actual Janus parent action and boundary data.

### P-B — anomaly filter

**Formalized in finite proxies:** PT pairing cancels the parity-odd contribution. Anomaly cancellation is independent of parity-even Helmholtz integrability and does not fix even couplings or finite even counterterms.

### P-C — Helmholtz reconstruction

**Formalized:** finite quadratic Hessian realizability is equivalent to formal self-adjointness; finite polynomial Helmholtz conditions reconstruct a cubic potential.

**Open:** derive the complete nonlinear Janus Euler source, Noether identities, nonlinear Helmholtz conditions, variational cohomology and boundary/null terms.

### P-D — invariant pairings and coefficient modules

**Formalized/audited:**

- `Z4` charge neutrality and PT selection rules;
- low-rank scalar/vector/tensor and spinor pairing dimensions;
- residual multiplicity-space matrices;
- closure under multiplication by invariant scalar coefficient functions;
- a counterexample showing that pointwise multiplicity one does not imply one constant global coupling;
- a counterexample showing invariant-fiber dimensions can jump between isotropy strata.

The correct global object is an equivariant pairing module over the invariant scalar algebra, not merely a pointwise Hom-space.

### P-E — finite jets, reduction, adapted frames and SpinC defects

The supported chain is now:

```text
regular + local
  -> locally finite-jet

finite-jet presentation + naturality
  <-> smooth equivariant evaluator

operator composition
  -> holonomic prolongation

structured action
  -> action groupoid + orbitwise descent

source/gauge quotient
  -> (B,F)

pointwise orthogonal splitting
  -> di = (id,0)

connection-corrected second jet
  -> B = II

smooth tangent/normal projectors
  -> smooth local adapted orthonormal frame

varying adapted frame
  -> exact connection correction and normal transport

frame overlaps
  -> O(T) x O(N) Čech cocycle

orientation characters
  -> SO(T) x SO(N) subcocycle

chosen central lifts + determinant roots
  -> matching ±1 defects
  -> SpinC diagonal cocycle

rank two
  -> U(1) --square--> U(1)
  -> U(1) ≃ SO(2)
  -> matrix Spin(2) double cover.
```

#### P-E results proved in Lean

- finite-jet naturality/equivariance and evaluator uniqueness;
- holonomic factorization of composite operators;
- action-groupoid laws, orbits and stabilizers;
- orbitwise descent from isotropy-fixed values;
- concrete second-order source action from the chain rule;
- concrete abelian connection gauge action and classification by curvature;
- exact combined quotient by `(B,F)`;
- universal factorization of invariant observables through `(B,F)`;
- pointwise tangent/normal orthogonal splitting;
- connection-corrected definition and coordinate invariance of `II`;
- exact flat-adapted identity `B = II`;
- residual `O(T) x O(N)` equivariance;
- joint smoothness and projector identities for tangent and normal projectors;
- smooth local adapted orthonormal frames by projected Gram--Schmidt;
- moving-frame raw two-jet formula;
- cancellation of derivative-of-frame terms by the transformed connection;
- canonical normal transport and moving-frame equivariance of `II`;
- identity, inverse and Čech laws for adapted-frame overlap transitions;
- determinant character and exact `SO(T) x SO(N)` residual subgroup;
- central double-cover lift defect, centrality and `±1` dichotomy;
- abstract SpinC diagonal defect cancellation;
- two-torsion of determinant square-root triple defects;
- concrete circle theorem `z²=1 -> z=±1`;
- surjective circle-squaring double cover with kernel `{±1}` and exact fibers;
- exact diagonal quotient and specialized rank-two SpinC cocycle theorem;
- explicit matrix equivalence `U(1) ≃ SO(2)`;
- surjective matrix-valued `Spin(2) -> SO(2)` projection with two-sheeted fibers.

#### Exact boundary

The local coordinate, overlap-cocycle and rank-two group calculations are exact. The repository has not yet:

- identified the circle model with Mathlib's even Clifford-algebra definition of `Spin(2)`;
- constructed the required higher-dimensional Clifford Spin covers;
- extracted all transition functions from actual smooth manifold frame bundles;
- constructed the global oriented and SpinC principal bundles;
- proved equality of the Spin obstruction and determinant-root obstruction for the actual Janus data;
- attached and glued the determinant-line connection;
- constructed the full differentiable structured-jet groupoid or effective descent for every natural sector.

Detailed statements and theorem names are recorded in [`program_pe_spinC_cocycle_lift.md`](program_pe_spinC_cocycle_lift.md).

### P-F — compatibility pullback

**Formalized:** a self-adjoint target Hessian pulls back through a compatibility-map linearization to a self-adjoint quadratic Helmholtz operator; gauge invariance gives the linearized Noether identity.

**Open:** construct the actual Janus compatibility complex, target pairing and global variational primitive.

## 6. Program P conclusion

```text
actual decorated Janus field/category data
  -> regular local finite-jet presentation
  -> structured jet groupoid and holonomic equivariant category
  -> low-order quotient (II,F)
  -> smooth local adapted orthonormal frame
  -> varying-frame tensorial law and oriented overlap cocycle
  -> central Spin and determinant-root defects
  -> SpinC diagonal cancellation
  -> concrete rank-two Spin(2)/SO(2) model
  -> higher Clifford Spin covers and characteristic-class matching
  -> higher reduced jets and integrability identities
  -> invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether + anomaly consistency
  -> action class and microscopic normalization
  -> stable vacuum and absolute scale
```

The repository does **not** yet contain the full smooth Janus structured-jet groupoid, the global Janus SpinC principal bundle, the higher-order jet-isomorphism theorem, a concrete global Janus Euler family, a selected parent action, a unique vacuum or an absolute no-fit scale.

## 7. Remaining lemma queue

The next open lemmas are:

1. **Clifford Spin(2) identification.** Identify the circle model with Mathlib's `CliffordAlgebra.spinGroup` for a two-dimensional Euclidean quadratic form.
2. **Clifford action theorem.** Prove that Clifford conjugation corresponds to the standard matrix `SO(2)` rotation and to circle squaring.
3. **Higher-dimensional Spin cover.** Instantiate the central double-cover data in the tangent and normal dimensions required by the Janus category.
4. **Bundle-packaging lemma.** Package projectors, adapted frames and transitions as sections and morphisms of actual manifold vector bundles.
5. **Smooth overlap lemma.** Prove smoothness of the extracted transition maps and construct the oriented principal frame bundle.
6. **Characteristic-class matching.** Prove equality of the Spin-lift defect and determinant square-root defect for the actual Janus tangent/normal/determinant data.
7. **Global SpinC bundle.** Construct the exact central fiber product, principal bundle and actions on tensor, spinor, twist and ghost sectors.
8. **Determinant-connection compatibility.** Identify the reduced curvature `F` with the curvature of the SpinC determinant-line connection.
9. **First covariant-derivative reduction.** Classify the next jet order by `nabla II`, `nabla F` and ambient curvature data.
10. **Gauss--Codazzi--Ricci--Bianchi theorem.** Characterize realizable reduced jets by algebraic and differential identities.
11. **Higher-order jet-isomorphism theorem.** Classify all finite structured jets by curvature data and covariant derivatives subject to integrability.
12. **Stratified equivariant extension.** Characterize smooth extension across higher-isotropy strata.
13. **Finite-generation/module theorem.** Under a proved compact/reductive residual action and a fixed polynomial/weight class, prove finite generation of invariant and equivariant modules.
14. **Concrete Helmholtz theorem.** Insert the resulting finite operator basis into the nonlinear Helmholtz system.

## 8. Immediate priorities

1. identify the concrete circle model with Clifford `Spin(2)`;
2. prove the matrix/Clifford action compatibility;
3. package the local frame and overlap constructions in actual vector bundles;
4. prove characteristic-class matching and construct the global SpinC bundle;
5. attach the determinant-line connection;
6. construct the finite-dimensional smooth structured-jet groupoid;
7. extend to `nabla II`, `nabla F` and Gauss--Codazzi--Ricci--Bianchi;
8. prove the higher-order structured jet-isomorphism theorem;
9. classify invariant modules and the concrete Helmholtz submodule.

## 9. Canonical navigation

- `PROGRAM.md` — stable high-level map;
- `docs/program_master_roadmap.md` — detailed dependency tree;
- `docs/program_pe_categorical_jet_equivalence.md` — corrected categorical theorem;
- `docs/program_pe_structured_jet_reduction.md` — action-groupoid and quotient program;
- `docs/program_pe_low_order_structured_background.md` — exact `(B,F)` quotient;
- `docs/program_pe_second_fundamental_form_jet.md` — pointwise `B = II` theorem;
- `docs/program_pe_smooth_adapted_frames.md` — smooth projectors and adapted frames;
- `docs/program_pe_spinC_cocycle_lift.md` — moving frames, oriented overlaps, SpinC defects and rank-two model;
- `docs/program_pd_global_pairing_modules.md` — pointwise-to-global coupling correction;
- `docs/janus_branch_registry.md` — supported heads and gate-only collections.
