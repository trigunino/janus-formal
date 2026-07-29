# Janus Branch and Build Registry

This file is operational. Scientific status lives in `docs/current_status.md`; this registry says which Lean entry points exist and how honestly they may be described.

## Status vocabulary

| Status | Meaning |
| --- | --- |
| **green** | focused CI passed on the current consolidation head |
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
| **D — fundamental geometry** | `lake build JanusFormal.Branches.FundamentalGeometryD` | **green** | mapping-torus, throat, monopole, Pin and geometry-to-physics gates |
| **D2 — twisted Dirac spectral geometry** | `lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral` | **green** | focused monopole spectrum, eta/holonomy, ratio correction and scale-orbit no-go |
| **D7 — spectral theory** | `lake build JanusFormal.Branches.FundamentalGeometryD7SpectralTheory` | **green** | heat coefficients, winding/determinant no-go results and conditional synthesis |
| **D8 — topology and representations** | `lake build JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation` | **green** | free analytic mapping torus, exact differential-normal `Diffeomorph` and canonical causal strata, ambient tangent orientation/quadratic transition data and genuine Clifford `Spin(Q) →* GL(4)` projection, normal principal `Pin⁻(1) ≃ Z4` bundle; the Program-P facade additionally constructs the ambient Pin⁻/PinC bundles and smooth intrinsic normal coordinates. General-metric causal classification and the final coordinate-presentation bridge remain open |
| **D9 — immersed SpinC elliptic complex** | `lake build JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex` | **green head** | P-independent symbol/linear-BRST closure, typed diagonal P-field projection and local D8-normal-section bridge with exact `-1 = Z4²`; the Program-P facade additionally constructs the actual doubled D9 spinor bundle, sections/connections, every signed smooth sphere/Fourier eigensection, exact multiplicities and orthogonality, Fourier--monopole completeness and the global geometric unitary. Its orientation-correct Hessian-label refinement intertwines the genuine smooth `2D+m²` core with a maximal self-adjoint Fredholm multiplier. Nonlinear ghost-difféo, the variable metric/gauge-coupled Dirac family and the remaining non-SpinC Hessian blocks remain open |
| **D10 — Quillen/anomaly** | `lake build JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly` | **green** | determinant-line/anomaly interfaces plus finite P-period product-mode/PT-regulator bridge; Hessian/regulator/common-domain agreement remains open |
| **D11 — natural immersion operators** | `lake build JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators` | **green head** | natural bundles, symbol calculus and finite-jet interfaces; global Fredholm family remains conditional |
| **P — variational principle** | `lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple` | **green** | `GEO/FIELD/ANALYSIS/BOUNDARY/KJ-01/KJ-02/NATURAL/ACTION/EULER/NOETHER/HELMHOLTZ/VARCOH-GLOBAL-01` closed on their documented domains; integrated scoped frontiers also cover the reduced ADM chain, constrained stability/vacuum no-go, symmetric actual Hessian, intrinsic/spectral Dirac, BRST/BV, D7/D10 regulator, circle Quillen geometry, PT/inflow anomaly, scheme freedom, microscopic-parent nonselection and the common-scale orbit. Continuum ADM/BD, physical quotient stability, selected microscopic parent/finite parts, unique effective vacuum, absolute scale and the common geometric Fredholm-family identification remain open. |
| **P-D — invariant pairings** | `lake build JanusFormal.Branches.FundamentalGeometryPEInvariantPairings` | **green** | low-rank invariant pairings, graded fusion rules and multiplicity-space freedom |
| **P-E — jet universality** | `lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality` | **green** | corrected regular-local finite-jet/equivariance theorem architecture |
| **P-F — compatibility/Helmholtz** | `lake build JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz` | **green** | pullback Hessian, nonlinear correction and Noether bridge |

## Main completion programs

| Program | Build | Status |
| --- | --- | --- |
| Quantum world-volume alpha | `lake build JanusFormal.Branches.WorldvolumeQuantumAlpha` | deep-alpha workflow green; physical stable vacuum and UV law remain conditional/open |
| Nonlinear bimetric junction alpha | `lake build JanusFormal.Branches.NonlinearBimetricJunctionAlpha` | deep-alpha workflow green; full constraints and null charge remain open |
| Alpha deep completion matrix | `lake build JanusFormal.Branches.AlphaDeepCompletionMatrix` | deep-alpha workflow green; no absolute no-fit scale |
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
