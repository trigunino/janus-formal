# Janus Formal — Master Roadmap

## Purpose

This document is the detailed dependency map for the current fundamental-geometry and variational programs. For merge state, CI truth and a concise scientific summary, read [`current_status.md`](current_status.md) first.

The repository does **not** currently claim:

- a complete global Janus geometry;
- a unique field content or action;
- a scheme-independent stable quantum vacuum;
- an absolute no-fit prediction of the Janus scale.

## Evidence labels

| Label | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python/symbolic audit |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic/geometric theorem represented by an interface |
| **N** | no-go result or correction |
| **O** | open theorem or construction |

## Complete dependency graph

```text
Program D — geometry, bundles and operators
├── D0/D8  mapping torus, one-sided throat, normal line and quarter lift
├── D2     focused twisted-Dirac spectral geometry
├── D7     heat kernel, winding determinants and scale no-go results
├── D9     gauge-fixed elliptic-symbol / BRST gate collection
├── D10    determinant-line, Quillen and anomaly interfaces
└── D11    natural bundles, symbols and finite-jet interfaces
          ↓
Program P — action selection and reconstruction
├── P0     moduli-geometry no-go
├── P-A    relative universal property / parent-bulk reduction
├── P-B    anomaly consistency and discrete selection
├── P-C    Helmholtz inverse variational problem
├── P-D    pointwise invariant pairings and global coefficient modules
├── P-E    finite jets, adapted frames, oriented overlaps and SpinC lifts
└── P-F    compatibility-map pullbacks, Helmholtz and Noether identities
          ↓
Programs A/B/C — quantum scale, nonlinear junction, charge compatibility
          ↓
Program E — observational falsification
```

The ordering is logical, not chronological. P-B and P-C are independent filters; P-A may supply the Euler family used by P-C; P-E supplies the local operator/jet category and its structured symmetry data; P-D classifies pointwise pairing shapes together with their invariant coefficient module; P-F explains one route by which compatibility geometry can inherit a variational pairing.

# Program D

## D0/D8 — Global geometry and normal lift

Candidate:

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),
Sigma ~ S2 x S1.
```

Current results:

- **T/C** the twisted generator squares to translation by `2T`;
- **T/N** nonzero translation is incompatible with a local fixed point of the same generator;
- **N** the candidate is a smooth mapping-torus model, not automatically a singular orbifold;
- **N** expected `pi_1` is `Z`, not `Z4`;
- **T/C** the normal clutching sign is `-1`, its doubled pullback is trivial, and the two complex square roots are `+i` and `-i`;
- **N** a real codimension-one line does not itself carry a literal quarter-turn;
- **N** a square-root line or `Z4` lift is extra global structure, not a canonical functor of the underlying line;
- **O** construct the actual global decorated mapping torus, throat embedding, ambient Pin structure and physical square-root bundle.

## D2 — Focused twisted Dirac spectral geometry

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral
```

Current results:

- **T/C/X** monopole-spectrum arithmetic and product pairing;
- **T/C** eta/holonomy relations and primitive-sector gap laws;
- **T/N** correction: `1/(2*sqrt(2))` is a compact-circle/sphere ratio, not `alpha/L_sphere`;
- **C** primitive compatibility can give `A=L_sphere` under the declared LL/bimetric inputs;
- **N** a common metric scale orbit survives;
- **O** construct the actual self-adjoint global operator, prove the spectrum/eta analytically and compute the full determinant.

Last focused CI: **green**.

## D7 — Heat kernel and effective action

- **T/X** local heat-kernel coefficients for the declared product-throat convention;
- **T/N** finite local truncations are affine in the circle modulus and cannot isolate a minimum;
- **T/X** local/nonlocal winding separation and quarter-phase cancellation structure;
- **N** pure and PT-paired quarter determinants do not stabilize the modulus;
- **N** a finite local coefficient can fit a chosen target and therefore is not predictive unless derived;
- **O** common zeta/eta regulator, complete field/ghost weights, finite renormalization and stable vacuum.

## D9 — Elliptic and BRST symbol gates

There is currently no supported standalone D9 head. The `Gates/` collection contains:

- tangent/normal immersion splitting;
- de Rham and Maxwell symbols;
- metric/de Donder and diffeomorphism-ghost symbols;
- normal Jacobi symbol;
- abstract Clifford/Dirac symbol;
- linear BRST and gauge-fixed block models.

These are local algebraic/symbol interfaces. They are not yet a global Fredholm complex on the Janus throat.

## D10 — Determinant line and anomalies

- **N** Quillen/Bismut–Freed is canonical only relative to a specified smooth Fredholm family;
- **N** determinant-line data do not choose field content, domains, finite counterterms or the scalar effective action;
- **I/O** construct the actual family index object, local/global anomaly, partition section and common regulator.

## D11 — Natural operators

There is currently no supported standalone D11 head. The gate collection formalizes:

- an abstract category of decorated immersions;
- natural bundle/section functors;
- natural operator and jet interfaces;
- principal-symbol composition/product closure;
- lower-order nonuniqueness;
- relative bridges to Quillen.

The concrete Janus category, global structured jet groupoid, regularity hypotheses, descent theorem and invariant-theory classification remain open.

# Program P

## P0 — Moduli-geometry no-go

- **T/N** the same metric supports different potentials and gradients;
- **T/N** the same symplectic form supports different Hamiltonians;
- **N** a Kähler-like package does not select a moment map or action.

## P-A — Relative action selection

- **T** a quadratic Hessian fixes an action only up to an affine functional;
- **T** Hessian + critical point + reference value yield unique normalized quadratic action;
- **T/C** a quadratic parent bulk problem yields a Schur-complement boundary action;
- **N** changing the parent action, boundary conditions or normalization changes the reduced action;
- **O** derive one actual Janus parent bulk/junction action.

## P-B — Anomaly filter

- **T** PT-paired anomaly proxies cancel;
- **T/N** anomaly cancellation leaves parity-even couplings and finite even counterterms free;
- **T/N** anomaly cancellation and Helmholtz integrability are logically independent;
- **C** discrete multiplicity selection requires independently fixed regulator data;
- **O** compute the actual local/global anomaly in the same field content and regulator used by the action.

## P-C — Helmholtz reconstruction

- **T** quadratic Hessian realizability iff formal self-adjointness in the finite models;
- **T** equal Hessians differ by affine terms;
- **T** PT plus normalization removes the quadratic affine ambiguity;
- **T** finite polynomial Helmholtz conditions reconstruct a cubic potential;
- **N** a Hessian at one background does not determine a global nonlinear action;
- **O** derive the complete Janus Euler source, Noether identities, nonlinear Helmholtz conditions, variational cohomology and boundary/null terms.

## P-D — Invariant pairings and global coefficient modules

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
```

Pointwise results:

- **T/X** `Z4` charge neutrality forbids same-quarter quadratic masses and allows the conjugate-quarter cross pairing;
- **T/X** scalar/vector/tensor low-rank pairing dimensions are computed in finite and symbolic models;
- **N** finite signed-permutation symmetry leaves two rank-five tensor quadratic forms;
- **T/X** adding a generic continuous rotation reduces the tensor self-pairing to the Frobenius contraction up to scale;
- **N** repeated irreducible sectors retain multiplicity-space matrices.

Global correction:

- **T** invariant background-dependent pairing families are closed under multiplication by invariant scalar coefficients;
- **T/N** an explicit finite Lean model has the same one-dimensional pointwise pairing shape at every background but no single constant global proportionality factor;
- **T/N** invariant-fiber dimensions can jump between isotropy strata;
- **N** pointwise `dim Hom = 1` does not imply one constant natural coupling;
- **O** construct the actual structured jet groupoid, invariant scalar algebra and global equivariant pairing module;
- **O** restrict the coefficient class by differential order, polynomial degree, weight, scale symmetry, Helmholtz conditions or a parent law.

Canonical correction document:

```text
docs/program_pd_global_pairing_modules.md
```

Last focused CI: **green**.

## P-E — Finite jets, adapted frames and SpinC lift data

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

Operator-by-operator statement:

> Fix natural source and target bundles. A regular local natural operator is locally represented by a smooth finite-jet evaluator. Under holonomic jet realization, naturality is equivalent to equivariance of that evaluator, and the evaluator is unique when realization is surjective.

Categorical correction:

> For ordinary finite-order natural or gauge-natural bundles, the classical category has jet-group actions as objects and equivariant maps from finite jet prolongations as morphisms. Composition uses holonomic prolongation. It is not the ordinary category of linear representations with plain fiber maps.

For decorated SpinC immersions the analogous equivalence is conditional on a structured jet groupoid over the background-jet space, an effective descent theorem and separation of global topological data.

### Proven local and algebraic chain

```text
regular local operator
  -> finite jet evaluator
  -> action groupoid and orbitwise descent
  -> source/gauge quotient (B,F)
  -> B = II in adapted coordinates
  -> smooth local adapted orthonormal frame
  -> varying-frame connection law and normal transport
  -> O(T) x O(N) overlap cocycle
  -> SO(T) x SO(N) determinant-one subcocycle
  -> central Spin-lift and determinant-root defects
  -> SpinC diagonal cancellation
  -> concrete circle Spin(2) double cover
  -> explicit U(1) ≃ SO(2) matrix equivalence
  -> metric-derived Euclidean Koszul connection
  -> projected-seed varying-normal atlas
  -> one-chart rank-two SpinC bundle/connection
  -> valid-chart low-order residual/SpinC action groupoid.
```

Current theorem evidence:

- **I** Peetre–Slovák supplies local finite-order factorization only under regularity/locality hypotheses;
- **T** naturality/equivariance equivalence and evaluator uniqueness in the formal action model;
- **T** holonomic factorization of composite evaluators;
- **T** action-groupoid laws and orbitwise descent;
- **T** concrete second-order immersion and abelian connection orbit classifications;
- **T** unique universal reduction through `(B,F)`;
- **T** pointwise and smooth local adapted-frame construction;
- **T** connection-corrected `B = II` and residual equivariance;
- **T** moving-frame second-jet law, connection cancellation and normal transport;
- **T** adapted-frame Čech cocycle and determinant-one `SO(T) x SO(N)` reduction;
- **T** central double-cover defects, determinant-root two-torsion and SpinC diagonal cancellation;
- **T** concrete circle squaring with kernel `{±1}`, exact fibers and diagonal quotient;
- **T** explicit group equivalence `U(1) ≃ SO(2)` and matrix-valued rank-two Spin double cover;
- **T** equivalence with Mathlib's rank-two Clifford Spin model;
- **T** smooth Euclidean Koszul connection existence from a smooth positive-definite metric;
- **T** projected-seed varying-normal atlas and overlap coefficient laws;
- **T** canonical one-chart rank-two SpinC Cech bundle and supplied-potential connection;
- **T** valid-chart low-order residual/SpinC action-groupoid realization;
- **T/N** local finite order need not give one global uniform order;
- **T/N** smooth dependence is not automatically polynomial;
- **N** equivariance plus finite-dimensionality does not by itself imply finite generation for nonreductive jet-group actions;
- **T/N** naturality does not imply ellipticity or field-content selection.

Exact remaining locks:

- **O** construct the required higher-dimensional Clifford Spin covers;
- **O** extend the projected-seed atlas and one-chart SpinC model to the actual
  nontrivial global Janus vector and principal bundles;
- **O** prove characteristic-class matching between the Spin and determinant-root defects;
- **O** identify the global determinant-line connection and attach every natural sector action;
- **O** construct the full differentiable structured jet groupoid and effective descent;
- **O** prove the higher-order jet-isomorphism and integrability theorem;
- **O** classify smooth equivariant maps across isotropy strata.

Canonical documents:

```text
docs/program_pe_categorical_jet_equivalence.md
docs/program_pe_low_order_structured_background.md
docs/program_pe_second_fundamental_form_jet.md
docs/program_pe_smooth_adapted_frames.md
docs/program_pe_spinC_cocycle_lift.md
```

Latest theorem-code validation: **green** at commit `1995bb68d5c06a1c627732f24ed27883c576ff36`, workflow run `29249977153`.

## P-F — Compatibility pullback, Helmholtz and Noether

Corrected bridge:

```text
compatibility map K
  -> linearization J
  + self-adjoint target pairing/Hessian H
  -> pulled-back Hessian J^T H J
```

- **T/C** the pulled-back finite model is self-adjoint and satisfies quadratic Helmholtz;
- **T/C** gauge invariance `K R = 0` yields a linearized Noether identity;
- **N** Gauss–Codazzi–Ricci–Bianchi compatibility alone does not imply Helmholtz;
- **N** off a target critical point, nonlinear second variation has an additional gradient-times-second-jet term;
- **O** construct the actual Janus compatibility jet complex, target pairing and global action primitive.

# Programs A/B/C and absolute scale

The strongest existing conditional chains transport dimensionless ratios and charge normalizations. The final absolute-scale prediction still requires all of:

- one selected parent/renormalized action;
- one unique stable vacuum;
- microscopic normalization and finite counterterms;
- equality of the spectral, LL, bulk and bimetric charge units;
- no observed-radius input.

# Supported heads and validation

| Entry | Status |
| --- | --- |
| `FundamentalGeometryDiracSpectral` | focused CI green |
| `FundamentalGeometryPEJetUniversality` | focused CI green through the rank-two matrix Spin layer |
| `FundamentalGeometryPEInvariantPairings` | focused CI green |
| `FundamentalGeometryD`, `D7`, `D8`, `D10`, `P`, `P-F` | focused CI green on consolidated main/active branch |
| D9 and D11 | gate collections; no supported standalone head |

See `current_status.md` and `janus_branch_registry.md` for the exact operational status.

# Shortest honest research path

```text
1. construct the actual decorated Janus category and field space;
2. choose induced/auxiliary/bulk metric formulation without double counting;
3. package local adapted frames and overlap cocycles in manifold bundles;
4. identify Clifford Spin covers and construct the global SpinC lift;
5. prove characteristic-class matching and attach the determinant connection;
6. construct the structured SpinC/PT/Z4/BRST jet groupoid and descent data;
7. prove the higher-order structured jet-normal-form/integrability theorem;
8. classify invariant scalar functions, global pairing modules and smooth equivariant evaluators;
9. derive one concrete compatible Euler family from a parent or microscopic law;
10. prove nonlinear Helmholtz, Noether and variational-cohomology closure;
11. compute anomalies in the same regulator and field content;
12. fix action normalization and finite counterterms microscopically;
13. compute the renormalized effective action and prove one stable vacuum;
14. close charge compatibility and the absolute scale.
```
