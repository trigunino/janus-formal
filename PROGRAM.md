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
| **D — Fundamental geometry** | derive throat, Pin/Z4, gauge and spectral data from one PT-twisted geometry | top-priority unification program | `JanusFormal.Branches.FundamentalGeometryD` |
| **A — Quantum world-volume** | generate the dimensionful LL charge and stable vacuum | absolute-scale generator | `JanusFormal.Branches.WorldvolumeQuantumAlpha` |
| **B — Nonlinear bimetric junction** | derive the common action, constraints, PT charge and bridge junction | classical/geometric consistency | `JanusFormal.Branches.NonlinearBimetricJunctionAlpha` |
| **C — Charge compatibility** | identify bulk, throat, LL and bridge charge normalizations | interface between D/A/B | `JanusFormal.Branches.AlphaDeepCompletionMatrix` |
| **E — Observation** | test derived predictions against SN, BAO, CMB, lensing and structure | falsification after theory closure | branch-specific runners |

## Dependency graph

```text
D1 global geometry and throat
 ├─ D2 Pin / geometric Z2 / fermionic Z4
 ├─ D3 throat monopole and compact transgression
 └─ D4 spectral operator
       ├─ A quantum effective action and dimensionful scale
       ├─ B nonlinear bimetric boundary charge
       └─ C normalization compatibility
             └─ absolute A
                   └─ E observational tests
```

Programs A and B are serial at final closure: B fixes the bridge relation, while
A fixes the dimensionful unit. C proves that both use the same charge.

## Current strongest conditional chain

The Program-D Dirac/Z4 branch currently proves the following algebraic chain
from explicit inputs:

```text
primitive monopole |n|=1
+ quarter Pin/Z4 circle holonomy
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

1. the global Pin lift really imposes quarter holonomy;
2. the separated monopole Dirac spectrum and eta formula hold for the actual
   throat operator;
3. the two-fold parity-even charge is exactly the sum of the two squared gaps;
4. a quantum or gravitational law fixes `L` absolutely.

## Stable entry points

1. `README.md`
2. `PROGRAM.md`
3. `docs/research_dashboard.md`
4. `docs/janus_branch_registry.md`
5. the selected program document under `docs/program_*`
6. the corresponding Lean branch head

## Repository rule

Every new proposal must record:

- program and stable ID;
- evidence level;
- inputs and dependencies;
- theorem or no-go obtained;
- remaining physical atom;
- falsification criterion;
- Lean/Python build target.
