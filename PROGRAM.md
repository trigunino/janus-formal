# Janus Research Program

This file is the stable top-level map of the repository. It is intentionally
short. Detailed matrices, evidence and blockers live under `docs/`.

## Scientific target

Derive the Janus geometry, field content, charge normalization and cosmological
scale from explicit mathematical and physical laws, without importing an
observed value of `H0`, `alpha`, a bridge radius or an equivalent hidden scale.

The positive length denoted `alpha^2` in the 2018 exact solution is called
`A = alphaSquaredLength` in the current research branches.

## Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **C** | conditional theorem: conclusion proved from named physical inputs |
| **G** | geometric construction target |
| **P** | physical/QFT derivation target |
| **N** | no-go or obstruction |
| **O** | observational test only |

No claim may move from `C`, `G` or `P` to `T` without replacing its opaque input
by an actual construction or theorem.

## Program matrix

| Program | Purpose | Current role | Head |
| --- | --- | --- | --- |
| **D — Fundamental geometry** | derive throat, gauge and charge data from one PT-twisted geometry | geometric seed | `JanusFormal.Branches.FundamentalGeometryD` |
| **D7 — Spectral theory** | derive heat-kernel, determinant, eta and effective-action data | quantum/spectral completion | `JanusFormal.Branches.FundamentalGeometryD7SpectralTheory` |
| **D8 — Topology and representations** | determine what the mapping torus actually forces before assigning orbifold or field-content claims | topology/representation audit | `JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation` |
| **A — Quantum world-volume** | generate the dimensionful LL charge and stable vacuum | absolute-scale generator | `JanusFormal.Branches.WorldvolumeQuantumAlpha` |
| **B — Nonlinear bimetric junction** | derive the common action, constraints, PT charge and bridge junction | classical/geometric consistency | `JanusFormal.Branches.NonlinearBimetricJunctionAlpha` |
| **C — Charge compatibility** | identify bulk, throat, LL and bridge charge normalizations | interface between D/A/B | `JanusFormal.Branches.AlphaDeepCompletionMatrix` |
| **E — Observation** | test derived predictions against SN, BAO, CMB, lensing and structure | falsification after theory closure | branch-specific runners |

## Dependency graph

```text
D8 topology/representation audit
  -> D1 smooth mapping torus and one-sided throat
       ├─ D2 Pin lift and orientation-local-system Z4
       ├─ D3 throat monopole and compact transgression
       └─ D7 actual field bundles and spectral operator
             ├─ A quantum effective action and dimensionful scale
             ├─ B nonlinear bimetric boundary charge
             └─ C normalization compatibility
                   -> absolute A
                         -> E observational tests
```

Programs A and B are serial at final closure: B fixes the bridge relation, while
A fixes the dimensionful unit. C proves that both use the same charge.

## D8 correction to the topology language

For the current candidate

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translation makes the integer action fixed-point free. The current object
is therefore best treated as a smooth nonorientable mapping torus, not as an
orbifold with a singular equatorial locus.

Its equatorial `S2 x S1` throat is expected to be one-sided. The orientation
cover has two exchanged sides, while the quotient has no global side label.
Consequently:

```text
cover : quotient = 2 : 1,
world A : world B = 1 : 1  under deck symmetry.
```

The expected fundamental group is `Z`, not `Z4`. Quarter holonomy can arise as
one of the two fourth-root lifts of the orientation character, but its order is
the order of the holonomy image, not the order of the fundamental group. The
cyclic topology also does not select a rank-five field multiplet.

## Current strongest conditional chain

The Program-D Dirac/Z4 branch currently proves the following algebraic chain
from explicit inputs:

```text
primitive monopole |n|=1
+ chosen quarter lift of the orientation/Pin monodromy
+ unweighted spectral modulus T^2=2*pi^2
    -> unique squared Dirac gap: gap^2 L^2 = 1/8

PT pair:
  eta_+ + eta_- = 0
  gap_+^2 + gap_-^2 = 2 gap^2
    -> q_LL L^2 = 1/4
    -> q_LL = lambda_S2 / 8

primitive LL flux:
  16 q_LL^2 A^4 = 1
    -> A = L
```

This is a **conditional compatibility theorem**, not yet an absolute-scale
prediction. The physical inputs still requiring derivation are:

1. the smooth mapping-torus and one-sided-throat topology is constructed;
2. the Pin convention and physical PT square are matched explicitly;
3. the chosen quarter lift is derived rather than inserted;
4. the actual field bundle and its rank are derived independently of cyclic
   holonomy;
5. the monopole Dirac spectrum and eta formula hold for the global operator;
6. the two-fold parity-even charge is exactly the sum of the two squared gaps;
7. a quantum or gravitational law fixes `L` absolutely.

## Stable entry points

1. `README.md`
2. `PROGRAM.md`
3. `docs/research_dashboard.md`
4. `docs/janus_branch_registry.md`
5. `docs/program_d8_topology_representation_audit.md`
6. the selected program document under `docs/program_*`
7. the corresponding Lean branch head

## Repository rule

Every new proposal must record:

- program and stable ID;
- evidence level;
- inputs and dependencies;
- theorem or no-go obtained;
- remaining physical atom;
- falsification criterion;
- Lean/Python build target.
