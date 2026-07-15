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

### P-A verdict

A parent variational problem gives a canonical throat action **relative to that parent problem**. Different parent actions, normalizations or boundary terms give different reduced actions.

**Open:** derive one actual bulk/junction action and its admissible boundary problem without target-scale input.

## 5. P-B — Anomaly consistency and discrete selection

### 5.1 Positive result

PT pairing reverses the parity-odd anomaly proxy, so the paired anomaly cancels.

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
finite coordinate pairing.

**Lean:** `P0EFTJanusFiniteRankPolynomialHelmholtz.lean`
**Evidence:** **T** coefficient-level; no global variational cohomology.

More generally, on an open convex real normed configuration domain, a
differentiable Euler one-form with symmetric actual Jacobian admits a scalar
action whose Fréchet derivative is that one-form. On the whole space, the
straight-segment integral gives an explicit primitive normalized at a chosen
base point. Any two such actions on a nonempty convex domain differ by a
constant, so fixing one base value removes this ambiguity. This is a
configuration-space Poincaré lemma, not the local PDE variational bicomplex.

**Lean:** `P0EFTJanusConvexHelmholtzReconstruction.lean`
**Evidence:** **T/C** on open convex configuration domains.

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
- for nonlinear `K`, the complete second variation equals `J^T H J` only at a target critical point; off shell there is a gradient-times-second-jet correction.

**Lean head:**

```text
lake build JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz
```

### P-F verdict

Compatibility geometry can transmit a variational structure supplied by a target pairing/action. It cannot create that pairing from compatibility identities alone.

The synthesis assumes the abstract algebraic complex and target pairing; it
does not construct the concrete nonlinear Janus compatibility complex.

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

The next concrete theorem package is not another abstract action proxy. It is:

1. define the exact Janus fields and gauge symmetries;
2. choose induced, auxiliary or bulk metric formulation without double counting;
3. build the actual compatibility map `K` and its jet linearization `J`;
4. derive a target pairing/Hessian `H` from a parent or microscopic action;
5. classify all invariant pairings in the actual symmetry category;
6. prove the concrete Euler family satisfies nonlinear Helmholtz and Noether identities;
7. compute variational cohomology, boundary terms and anomalies in one scheme;
8. derive normalization and finite counterterms without observed-radius input.

## 13. Honest conclusion

Program P has substantially reduced the logical freedom, but it has not selected the physical Janus action.

The finite two-field polynomial P-C model now proves the exact equivalence
between Helmholtz compatibility of a quadratic Euler system and realization as
the gradient of a cubic potential. This does not discharge the nonlinear Janus
Helmholtz or variational-cohomology obligations.

What is established is a theorem/no-go architecture explaining exactly which inputs are needed and which proposed shortcuts fail. The decisive missing object is a concrete global Janus parent/target variational problem whose compatible Euler family can pass P-D/P-E/P-F classification and P-C/P-B consistency tests.
