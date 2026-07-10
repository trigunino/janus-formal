# Janus Branch Registry

This file is the navigation surface for active and parked research branches.
Build one branch head at a time.

## Shared Libraries

| Module | Build | Status |
| --- | --- | --- |
| `JanusFormal.Core` | `lake build JanusFormal.Core` | no-Mathlib shared kernel |
| `JanusFormal.Shared.Foundation` | `lake build JanusFormal.Shared.Foundation` | branch-safe foundation facade |
| `JanusFormal.Shared.MathCompat` | `lake build JanusFormal.Shared.MathCompat` | Mathlib compatibility for older modules |

## Branch Heads

| Branch | Build | Status |
| --- | --- | --- |
| Alpha bridge state law / superselection | `lake build JanusFormal.Branches.AlphaBridgeStateLaw` | viable only as state-sector selection; no no-fit alpha law |
| RP4 twisted four-form alpha | `lake build JanusFormal.Branches.RP4TwistedFourFormAlpha` | orientation-twisted flux and primitive odd-sector selector proved; charge unit, map to published dust-like `E_global`, and Lorentzian scale matching remain open |
| Native BAO/ruler contract | `lake build JanusFormal.Branches.NativeBAORulerContract` | formulated; blocked by missing native early-time/ruler primitives |
| Early-time orbifold ruler | `lake build JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler` | projected photon-baryon plasma pushed to formula-complete/input-blocked frontier; other BAO/ruler routes documented as blocked |
| Early-universe native plasma | `lake build JanusFormal.Branches.JanusEarlyUniverseNativePlasma` | pushed to final early/late matching frontier; entropy cutoff can reach `z=1000`, but same late cosh branch and two-cosh throat gluing do not close without a new transition law or early `H_J(a)` |
| Projective point PT limit | `lake build JanusFormal.Branches.JanusProjectivePointPTLimit` | opened as non-throat limit; removes finite Sigma-radius obligations but requires a singular/projective initial law and native early ruler |
| Non-throat PT transitions | `lake build JanusFormal.Branches.JanusNonThroatPTTransitions` | final frontier reached: Weyl-cusp domain, `g(+)` kinematics, `S4/RP4` conformal background, bimetric source contract, global conservation Omega relation, and 00 projection are closed; no internal route fixes `L/E_global`, Lorentzian time, pre-drag scalings, or Omega boundary data |
| Regular Z2/Sigma throat | `lake build JanusFormal.Branches.Z2SigmaRegularThroat` | blocked by missing non-rustine scale/source closure |
| Null Sigma / PT bridge | `lake build JanusFormal.Branches.NullPTBridgeMass` | blocked by missing derived bridge mass/LL state law |
| Quantum boundary state law | `lake build JanusFormal.Branches.QuantumBoundaryStateLaw` | conditional spectra possible; no derived alpha selector |
| Complex-reality quantum state law | `lake build JanusFormal.Branches.ComplexRealityQuantumStateLaw` | exploratory; no closed boundary mass law |
| Asymptotic null-boundary charges | `lake build JanusFormal.Branches.AsymptoticNullBoundaryCharges` | audited; no derived boundary mass/alpha charge |
| Candidate mechanism matrix | `lake build JanusFormal.Branches.CandidateMechanismMatrix` | matrix of exits; all alpha routes and route combinations pushed to explicit frontier; no no-fit state law closed |
| Alpha sector theory | `lake build JanusFormal.Branches.AlphaSectorTheory` | baseline sector audit; alpha remains external |
| CMB/Planck diagnostic attempts | `lake build JanusFormal.Branches.CMBPlanckDiagnosticAttempts` | CAMB/Planck attempts; blocked as active evidence |
| Z4 CMB topology-reset blocked program | `lake build JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram` | Z4/CMB solver route; blocked by geometry/topology reset |
| P0 bimetric/orbifold prototype program | `lake build JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram` | light inventory head for bimetric/orbifold prototypes |
| P0EFT orbifold/Holst prototype program | `lake build JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram` | light inventory head for EFT/orbifold/Holst prototypes |

## Rules

- Do not use a global all-import build as normal workflow.
- Add a branch head under `JanusFormal/Branches/` for each branch.
- Put reusable primitives under `JanusFormal/Shared/` or `JanusFormal/Core.lean`.
- Keep every attempt, including old/blocked attempts, under an explicit branch.
- Do not use catch-all old-attempt folders; put the status/blocker in this
  registry instead.
