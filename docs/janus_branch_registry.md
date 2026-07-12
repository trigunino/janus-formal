# Janus Branch and Build Registry

This file is operational. Scientific status lives in `docs/current_status.md`; this registry says which Lean entry points exist and how honestly they may be described.

## Status vocabulary

| Status | Meaning |
| --- | --- |
| **green** | focused CI passed on the last checked merged head |
| **present / revalidation required** | entry file exists, but the post-merge focused build has not yet passed |
| **integration red** | a broad workflow including the head failed |
| **gate collection** | modules exist under `Gates/`, but no supported standalone head exists |
| **parked** | retained for history or an alternative route; not the current priority |

## Shared libraries

| Module | Build | Status |
| --- | --- | --- |
| `JanusFormal.Core` | `lake build JanusFormal.Core` | lightweight shared core |
| `JanusFormal.Shared.Foundation` | `lake build JanusFormal.Shared.Foundation` | branch-safe foundation facade |
| `JanusFormal.Shared.MathCompat` | `lake build JanusFormal.Shared.MathCompat` | compatibility layer for older modules |

## Canonical fundamental-program entries

| Program | Build / location | Status | Scope |
| --- | --- | --- | --- |
| **D — fundamental geometry** | `lake build JanusFormal.Branches.FundamentalGeometryD` | **integration red** | mapping-torus, throat, monopole, Pin and geometry-to-physics gates |
| **D2 — twisted Dirac spectral geometry** | `lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral` | **green** | focused monopole spectrum, eta/holonomy, ratio correction and scale-orbit no-go |
| **D7 — spectral theory** | `lake build JanusFormal.Branches.FundamentalGeometryD7SpectralTheory` | **present / revalidation required** | heat coefficients, winding/determinant no-go results and conditional synthesis |
| **D8 — topology and representations** | `lake build JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation` | **present / revalidation required** | free mapping torus, one-sided throat, normal line and quarter-lift audits |
| **D9 — immersed SpinC elliptic complex** | `JanusFormal/Branches/FundamentalGeometryD9ImmersedSpinCEllipticComplex/Gates/` | **gate collection** | symbol-level immersion, de Rham/Maxwell, metric/ghost and twisted-Dirac modules; no supported head yet |
| **D10 — Quillen/anomaly** | `lake build JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly` | **present / revalidation required** | determinant-line, anomaly and partition-section interfaces |
| **D11 — natural immersion operators** | `JanusFormal/Branches/FundamentalGeometryD11NaturalImmersionOperators/Gates/` | **gate collection** | natural bundle, symbol and jet interfaces; no supported head yet |
| **P — variational principle** | `lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple` | **present / revalidation required** | P0, P-A, P-B, P-C and invariant-pairing interfaces |
| **P-E — jet universality** | `lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality` | **green** | corrected regular-local finite-jet/equivariance theorem architecture |
| **P-D / P-E pairings** | `JanusFormal/Branches/FundamentalGeometryPEInvariantPairings/Gates/` and P-head gates | **gate collection + executable audits** | low-rank invariant pairings and graded fusion rules; no standalone head yet |
| **P-F — compatibility/Helmholtz** | `lake build JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz` | **present / revalidation required** | pullback Hessian, nonlinear correction and Noether bridge |

## Main completion programs

| Program | Build | Status |
| --- | --- | --- |
| Quantum world-volume alpha | `lake build JanusFormal.Branches.WorldvolumeQuantumAlpha` | conditional algebra advanced; stable renormalized vacuum and UV law open |
| Nonlinear bimetric junction alpha | `lake build JanusFormal.Branches.NonlinearBimetricJunctionAlpha` | conditional classical chain advanced; full constraints and null charge open |
| Alpha deep completion matrix | `lake build JanusFormal.Branches.AlphaDeepCompletionMatrix` | compatibility/dependency matrix; no absolute no-fit scale |
| RP4 twisted four-form alpha | `lake build JanusFormal.Branches.RP4TwistedFourFormAlpha` | retained alternative topological sector |
| PT-twisted Hopf geometry | `lake build JanusFormal.Branches.JanusTwistedHopfGeometry` | retained geometric candidate; global analytic construction open |

## Parked and diagnostic programs

| Branch | Build | Status |
| --- | --- | --- |
| Alpha bridge state law / superselection | `lake build JanusFormal.Branches.AlphaBridgeStateLaw` | parked; state-sector selection only |
| Native BAO/ruler contract | `lake build JanusFormal.Branches.NativeBAORulerContract` | parked; missing native early-time/ruler primitives |
| Early-time orbifold ruler | `lake build JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler` | parked/input-blocked |
| Early-universe native plasma | `lake build JanusFormal.Branches.JanusEarlyUniverseNativePlasma` | parked; missing transition/early expansion law |
| Projective point PT limit | `lake build JanusFormal.Branches.JanusProjectivePointPTLimit` | alternative non-throat limit |
| Non-throat PT transitions | `lake build JanusFormal.Branches.JanusNonThroatPTTransitions` | alternative transition program; absolute inputs open |
| Regular Z2/Sigma throat | `lake build JanusFormal.Branches.Z2SigmaRegularThroat` | parked/blocked |
| Null Sigma / PT bridge | `lake build JanusFormal.Branches.NullPTBridgeMass` | parked/blocked |
| Quantum boundary state law | `lake build JanusFormal.Branches.QuantumBoundaryStateLaw` | exploratory |
| Complex-reality quantum state law | `lake build JanusFormal.Branches.ComplexRealityQuantumStateLaw` | exploratory |
| Asymptotic null-boundary charges | `lake build JanusFormal.Branches.AsymptoticNullBoundaryCharges` | audited/no derived alpha charge |
| Candidate mechanism matrix | `lake build JanusFormal.Branches.CandidateMechanismMatrix` | inventory/no closed selector |
| Alpha sector theory | `lake build JanusFormal.Branches.AlphaSectorTheory` | baseline audit |
| CMB/Planck diagnostic attempts | `lake build JanusFormal.Branches.CMBPlanckDiagnosticAttempts` | diagnostics only |
| Z4 CMB topology-reset blocked program | `lake build JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram` | blocked diagnostic route |
| P0 bimetric/orbifold prototype | `lake build JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram` | light inventory head |
| P0EFT orbifold/Holst prototype | `lake build JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram` | light inventory head |

## Rules

- Build one focused head at a time.
- Do not infer that a `Gates/` directory has a valid head.
- Do not call a head green without a focused passing workflow or reproducible local build.
- Do not use a global all-import build as the normal workflow.
- Put reusable primitives under `JanusFormal/Shared/` or `JanusFormal/Core.lean`.
- Keep blocked or superseded attempts, but label them explicitly rather than presenting them as active closure paths.
