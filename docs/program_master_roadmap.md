# Janus Formal — Master Roadmap

## Purpose

This is the main entry point for the fundamental-geometry branch. It separates proved results, executable checks, conditional statements and open research gates across Programs D, P and P.E.

The branch does **not** claim a complete physical Janus theory, a unique quantum action or a numerical no-fit prediction.

## Evidence labels

| Label | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python audit or numerical consistency test |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic/geometric theorem used as an interface |
| **N** | no-go or correction of an over-strong claim |
| **O** | open theorem or construction |

## Dependency graph

```text
Program D — geometry and spectral foundations
├── D0   global mapping-torus candidate
├── D7   spectral and effective-action layer
├── D8   topology, normal line, Pin/SpinC and Z4 lift
├── D9   elliptic complexes and principal symbols
├── D10  Quillen and anomaly interfaces
└── D11  natural operators
        ↓
Program P — variational selection
├── P0   moduli-geometry no-go
├── P-A  relative universal property / parent-bulk reduction
├── P-B  anomaly consistency and discrete selection
├── P-C  Helmholtz reconstruction
└── P-D  invariant pairings and remaining couplings
        ↓
Program P.E — jets and representations
├── P.E-Pairings  invariant/graded pairings
└── P.E-Jets      locality → finite jets → equivariant evaluators
```

# Program D

## D0 — Global geometry

Target:

```text
J(T,rho) = (S3 x R) / ((x,u) ~ (rho(x),u+T)),
Sigma ~ S2 x S1.
```

- **T/C** twisted generator squares to translation by `2T`.
- **C** nonzero translation removes fixed points from the mapping-torus action.
- **N** expected `pi_1` is `Z`, not `Z4`.
- **N** `Z4` is a lift/holonomy representation, not directly the fundamental group.
- **O** construct the full global decorated SpinC mapping torus and throat embedding.

## D7 — Spectral and effective action

- **T/X** local heat-kernel coefficients for the declared product-throat convention.
- **T** every finite local truncation is affine in the circle modulus.
- **T/X** winding separation and quarter-phase cancellations.
- **N** pure and PT-paired quarter determinants do not stabilize the modulus.
- **O** global Dirac operator, full spectrum, common zeta/eta regulator, field/ghost weights and stable vacuum.

## D8 — Normal line and Z4 lift

- **T** normal clutching sign is `-1`.
- **T** doubled pullback is trivial.
- **T** complex square roots are `+i` and `-i`.
- **T** one/two/four loops give quarter/central-sign/periodic behavior.
- **N** a real codimension-one line alone does not carry a literal quarter-turn.
- **O** construct the ambient Pin structure and identify the physical square-root bundle.

## D9 — Elliptic complexes

- **T** `Sym^2(T*Sigma) = trace 1 + traceless 5` in dimension three.
- **T/C** symbol-level de Rham, gauge, metric, normal and Dirac blocks.
- **N** induced metric variation is not independent of immersion variation.
- **O** choose a consistent metric formulation and build the global Fredholm complex.

## D10 — Quillen and anomalies

- **N** Quillen is canonical only relative to a chosen Fredholm family.
- **N** it does not choose field content, domains or finite renormalization.
- **O** construct the actual determinant line and compute local/global anomalies.

## D11 — Natural operators

- **T/C** abstract decorated-immersion category and natural-symbol interfaces.
- **N** principal symbols do not fix lower-order terms.
- **O** instantiate the exact Janus category, bundles and natural operator families.

# Program P

## P0 — Moduli-geometry no-go

- **T/N** the same metric supports different potentials and gradients.
- **T/N** the same symplectic form supports different Hamiltonians.
- **N** metric/symplectic/Kähler-like geometry alone does not select an action.

## P-A — Relative universal property

- **T** a Hessian fixes a quadratic action only up to an affine term.
- **T** Hessian + critical point + reference value give a unique quadratic action.
- **T/C** a parent quadratic bulk action induces a Schur-complement boundary action.
- **N** changing the parent theory or boundary terms changes the selected action.

## P-B — Anomaly selection

- **T** PT pairing cancels the parity-odd anomaly proxy.
- **T/N** anomaly cancellation does not determine parity-even couplings.
- **T/C** discrete multiplicity selection requires externally fixed regulator data.
- **N** P-B is a consistency filter, not a complete dynamics principle.

## P-C — Helmholtz reconstruction

- **T** finite quadratic Hessian realizability is equivalent to formal self-adjointness.
- **T** equal Hessians differ by affine terms.
- **T** PT plus normalization removes the quadratic ambiguity.
- **T** polynomial Helmholtz conditions reconstruct a cubic potential in the finite model.
- **O** derive the complete Janus Euler source and prove nonlinear Helmholtz, Noether and variational-cohomology conditions.

## P-D — Invariant pairings

- **T/X** finite invariant/graded pairing models are implemented.
- **N** PT and Helmholtz still leave same-parity couplings.
- **O** compute the actual spaces `Hom_G(E_i tensor E_j, R)` and connect them to the D9/D11 Fredholm family.

# Program P.E

## P.E-Pairings

Goal:

```text
natural sectors → representations → invariant pairings → Hessian candidates
```

- **T/X** executable finite-sector pairing audits exist.
- **N** pairing multiplicities cannot be known before the exact group and representations are fixed.
- **O** build the SpinC/PT/Z4/BRST-graded Janus representation category.

## P.E-Jets — Corrected finite-jet theorem

> Fix natural source and target bundles. A regular local natural operator is locally represented by a smooth finite-jet evaluator. Under holonomic jet realization, naturality is equivalent to equivariance of that evaluator, and the evaluator is unique when realization is surjective.

- **I** Peetre–Slovák supplies local finite-order factorization under regularity and locality.
- **T** naturality/equivariance equivalence in the formal action model.
- **T** evaluator uniqueness under surjective jet realization.
- **T/N** local finite order need not admit one global uniform bound.
- **T/N** smooth natural dependence is not automatically polynomial.
- **T/N** naturality does not imply ellipticity.
- **O** define the actual decorated Janus SpinC jet group and classify its smooth equivariant maps.

Precise documents:

```text
docs/program_pe_jet_universality_proof.md
docs/program_pe_lemma2_naturality_equivariance.md
```

# Stable heads and checks

```text
lake build JanusFormal.Branches.FundamentalGeometryD
lake build JanusFormal.Branches.FundamentalGeometryD7SpectralTheory
lake build JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation
lake build JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

Python audits include the geometry, spectral, invariant-pairing, spinor-pairing and finite-jet universality checks under `scripts/audit_janus_*.py`.

# Current frontier

The shortest honest route to a selected Janus action is:

```text
actual decorated SpinC category
→ finite-jet factorization and adapted symmetry group
→ equivariant invariant/covariant classification
→ natural elliptic Euler family
→ nonlinear Helmholtz and variational cohomology
→ anomaly consistency
→ normalization and finite renormalization law
→ selected action and stable vacuum
```

The next theorem target is the Janus specialization of Program P.E-J:

1. construct the adapted SpinC/PT/Z4/BRST jet symmetry group;
2. define the actual source and target natural bundles;
3. verify locality, regularity and holonomic realization;
4. classify smooth equivariant evaluators at bounded jet order;
5. impose ellipticity, Helmholtz and anomaly constraints separately.
