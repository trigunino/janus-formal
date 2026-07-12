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
├── P-D    invariant pairings and residual coupling spaces
├── P-E    regular-local finite jets and equivariant evaluators
└── P-F    compatibility-map pullbacks, Helmholtz and Noether identities
          ↓
Programs A/B/C — quantum scale, nonlinear junction, charge compatibility
          ↓
Program E — observational falsification
```

The ordering is logical, not chronological. P-B and P-C are independent filters; P-A may supply the Euler family used by P-C; P-D/P-E classify its admissible local structure; P-F explains one route by which compatibility geometry can inherit a variational pairing.

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

Last focused CI: **green** on the merged D2 head.

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

The concrete Janus category, regularity hypotheses and invariant-theory classification remain open.

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

## P-D — Invariant pairings

- **T/X** `Z4` charge neutrality forbids same-quarter quadratic masses and allows the conjugate-quarter cross pairing;
- **T/X** scalar/vector/tensor low-rank pairing dimensions are computed in finite and symbolic models;
- **N** finite signed-permutation symmetry leaves two rank-five tensor quadratic forms;
- **T/X** adding a generic continuous rotation reduces the tensor self-pairing to the Frobenius contraction up to scale;
- **N** repeated irreducible sectors retain multiplicity-space matrices;
- **O** globalize the pointwise pairings and compute the actual SpinC/PT/Z4/BRST multiplicities.

## P-E — Corrected finite-jet theorem

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

Correct statement:

> Fix natural source and target bundles. A regular local natural operator is locally represented by a smooth finite-jet evaluator. Under holonomic jet realization, naturality is equivalent to equivariance of that evaluator, and the evaluator is unique when realization is surjective.

Corrections retained:

- **I** Peetre–Slovák supplies local finite-order factorization only under regularity/locality hypotheses;
- **T** naturality/equivariance equivalence in the formal action model;
- **T** evaluator uniqueness under surjective realization;
- **T/N** local finite order need not give one global uniform order;
- **T/N** smooth dependence is not automatically polynomial;
- **T/N** naturality does not imply ellipticity or field-content selection;
- **O** construct the actual Janus jet symmetry group and classify its smooth equivariant maps.

Last focused CI: **green** on the merged P-E head.

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
| `FundamentalGeometryPEJetUniversality` | focused CI green |
| `FundamentalGeometryD`, `D7`, `D8`, `D10`, `P`, `P-F` | entry exists; post-consolidation focused revalidation required |
| D9, D11, P-D/P-E pairing collections | gates exist; no supported standalone head |

The broad Program-D integration workflow was red on the last pre-consolidation head. See `current_status.md` and `janus_branch_registry.md` for the exact operational status.

# Shortest honest research path

```text
1. construct the actual decorated Janus category and field space;
2. choose induced/auxiliary/bulk metric formulation without double counting;
3. construct adapted SpinC/PT/Z4/BRST jet and representation data;
4. classify invariant pairings and smooth equivariant evaluators;
5. derive one concrete compatible Euler family from a parent or microscopic law;
6. prove nonlinear Helmholtz, Noether and variational-cohomology closure;
7. compute anomalies in the same regulator and field content;
8. fix action normalization and finite counterterms microscopically;
9. compute the renormalized effective action and prove one stable vacuum;
10. close charge compatibility and the absolute scale.
```
