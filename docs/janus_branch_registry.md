# Janus Branch Registry

This file is the navigation surface for active and parked research branches.
Build one branch head at a time.

## Shared Libraries

| Module | Build | Status |
| --- | --- | --- |
| `JanusFormal.Core` | `lake build JanusFormal.Core` | no-Mathlib shared kernel |
| `JanusFormal.Lib.Foundation` | `lake build JanusFormal.Lib.Foundation` | branch-safe foundation facade |
| `JanusFormal.Lib.MathCompat` | `lake build JanusFormal.Lib.MathCompat` | Mathlib/legacy compatibility |

## Branch Heads

| Branch | Build | Status |
| --- | --- | --- |
| Bridge state law / alpha superselection | `lake build JanusFormal.Branches.BridgeStateLaw` | viable only as state-sector selection; no no-fit alpha law |
| Native BAO/ruler contract | `lake build JanusFormal.Branches.NativeBAORuler` | formulated; blocked by missing native early-time/ruler primitives |
| Regular Z2/Sigma throat | `lake build JanusFormal.Branches.Z2SigmaRegular` | blocked by missing non-rustine scale/source closure |
| Null Sigma / PT bridge | `lake build JanusFormal.Branches.NullPTBridge` | blocked by missing derived bridge mass/LL state law |
| Quantum boundary state | `lake build JanusFormal.Branches.QuantumBoundaryState` | conditional spectra possible; no derived alpha selector |
| Complex reality state law | `lake build JanusFormal.Branches.ComplexRealityStateLaw` | exploratory; no closed boundary mass law |
| Asymptotic null boundary | `lake build JanusFormal.Branches.AsymptoticNullBoundary` | audited; no derived boundary mass/alpha charge |
| New idea sector program | `lake build JanusFormal.Branches.NewIdeaSectorProgram` | matrix of exits; no closed state law |
| Sector theory V0 | `lake build JanusFormal.Branches.SectorTheoryV0` | baseline sector audit; alpha remains external |
| Historical CMB diagnostics | `lake build JanusFormal.Branches.CMBHistoricalDiagnostics` | old CAMB/Planck attempts; blocked as evidence, kept as branch |
| Historical Z4 program | `lake build JanusFormal.Branches.Z4HistoricalProgram` | old Z4/CMB solver route; blocked by geometry/topology reset, kept as branch |
| Early P0 program | `lake build JanusFormal.Branches.P0EarlyProgram` | first exploratory formal modules; kept as branch for traceability |
| Early P0EFT program | `lake build JanusFormal.Branches.P0EFTEarlyProgram` | old EFT/orbifold/Holst attempts; kept as branch for traceability |

## Rules

- Do not use a global all-import build as normal workflow.
- Add a branch head under `JanusFormal/Branches/` for each branch.
- Put reusable primitives under `JanusFormal/Lib/` or `JanusFormal/Core.lean`.
- Keep every attempt, including old/blocked attempts, under an explicit branch.
- Do not use `Legacy/` as a filesystem category; put the status/blocker in this
  registry instead.
