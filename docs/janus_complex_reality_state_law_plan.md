# Janus Complex Reality State Law Plan

## Branch

`janus_complex_reality_state_law`

## Purpose

Use `X2026-complex-reality` as a fundamental-state branch, not as a direct
cosmology branch.

The target is narrow:

- derive a global Janus state space;
- test whether Souriau/coadjoint geometry gives a nonzero KKS/symplectic density;
- test whether geometric quantization gives a sector lattice;
- test whether `alpha` can be mapped to a charge/orbit invariant instead of
  remaining a continuous integration/state label.

## Source Anchor

- `docs/source_cards/X2026-complex-reality.md`
- `data/raw/janus_library_text/X2026-complex-reality_the-real-world-as-a-part-of-a-complex-reality.txt`
- `C:/Users/alzie/Downloads/2026-07-07-Is the real world as a part of a complex reality.pdf`

The source is treated as a symmetry/Souriau roadmap. It is not treated as a
paper-native SN, BAO, CMB, or FLRW observable contract.

## Allowed Inputs

- complexified Minkowski/Hermite metric structure;
- complex Lorentz/Poincare group;
- adjoint/coadjoint action;
- anti-Hermitian complex moment objects;
- Souriau moment-map language;
- geometric quantization hints explicitly present in the source set;
- existing Janus/Z2 active core only as the target geometry for `alpha`.

## Forbidden Claims

- `alpha` is fixed;
- an observation is matched;
- a full FLRW background is emitted;
- a BAO ruler is derived;
- a CMB layer is opened;
- complex reality proves a new cosmology by itself.

## First Work Plan

1. Curate formula anchors from `X2026-complex-reality`.
2. Define the complex coadjoint moment space used by the paper.
3. Identify the real/Janus/PT slice relevant to mass sign and `alpha`.
4. Derive or reject a nonzero KKS two-form on the global/boundary state orbit.
5. If nonzero, test prequantization: periods of `Omega/(2*pi*hbar)` on relevant cycles.
6. If integral, derive a mass/charge lattice and a primitive sector law.
7. Map any derived mass/charge unit to the existing relation
   `alpha_m = -2*pi*G*M_boundary/c^2`.
8. If any step fails, record the exact blocker and keep `alpha` as a continuous
   global state sector.

## First Gate Targets

- `ComplexRealitySourceFormulaCurationGate`
- `ComplexRealityCoadjointStateSpaceGate`
- `ComplexRealityKKSBoundaryDensityGate`
- `ComplexRealityPrequantizationIntegralityGate`
- `ComplexRealityAlphaStateLawVerdictGate`

## Current Status

Open branch. No `alpha` prediction yet.

`ComplexRealitySourceFormulaCurationGate` is now the first completed step. It
curates the complex metric, complex Poincare group, Lie algebra action, moment
space, Souriau pairing, and coadjoint action anchors.

The document adds a concrete complex coadjoint-state scaffold. It does not yet
add the missing boundary phase space, nonzero KKS density, integrality periods,
mass/charge lattice, or primitive sector law.

`ComplexRealityEq131KKSProjectionGate` verifies the Eq. 131 issue. The published
formula is kept as source anchor, but direct KKS use must preserve
`M_dagger=-M`. The raw translation term is not generically anti-Hermitian;
the KKS-ready representative is the anti-Hermitian projection
`C P'_dagger L_dagger - L P' C_dagger`, matching the real appendix pattern.

`ComplexRealityCoadjointStateSpaceGate` closes the first real construction:
the complex coadjoint state space is declared and KKS-safe at the algebraic
level. It still does not derive the boundary KKS two-form on `Sigma`.

`ComplexRealityKKSBoundaryDensityGate` pushes the next layer. It finds a
nonzero finite-dimensional KKS form on the complex coadjoint orbit, using
`Omega_mu(ad*_X mu, ad*_Y mu)=<mu,[X,Y]>`. This is real progress: the source
does provide a nontrivial Souriau orbit geometry. It still does not provide a
nonzero `Sigma` boundary density, because the active map from boundary
variations to complex Poincare generators is not derived.

`ComplexRealitySigmaBoundaryProjectionGate` derives that map symbolically:
`gamma_Sigma^A(delta)=e^A_mu delta X^mu`,
`omega_Sigma(delta)=antiHermitian_G(delta L L^{-1})`, and
`Z_Sigma(delta)=(G omega_Sigma, gamma_Sigma;0,0)`. The KKS pullback density is
then `<mu,[Z_Sigma(delta1),Z_Sigma(delta2)]>`. This closes the symbolic
projection. The active nonzero density remains blocked until a nontrivial
boundary variation basis and closed two-cycle are derived.

Lean formalization is now present in `JanusFormal.Branches.ComplexRealityQuantumStateLaw`.
It imports the source curation, Eq. 131 projection, coadjoint state-space,
KKS boundary-density, and Sigma boundary-projection gates. The formal status
matches the scripts: symbolic branch ready, active density and `alpha`
generation still blocked.

`ComplexRealityBoundaryVariationBasisGate` adds the next symbolic layer:
normal embedding displacement, frame rotation/boost, and connection holonomy
are declared as the candidate boundary variation channels, while tangential
displacement is treated as gauge. This does not yet activate the KKS density:
active embedding values and a closed boundary two-cycle are still missing.

`ComplexRealityClosedBoundaryTwoCycleGate` now audits the cycle candidates.
The throat angular `S2` is a closed topological two-cycle and `aroundSigma`
is a closed Z2 one-cycle. This is still not a KKS phase-space two-cycle with
a nonzero `Omega_Sigma` period. The next hard object is either an active
embedding pullback that evaluates the density on the throat `S2`, or a derived
compact frame/phase direction pairing with `aroundSigma`.

`ComplexRealityActiveEmbeddingOrCompactPhaseGate` makes the remaining fork
explicit. Route A is an active embedding/coframe pullback evaluation of
`Omega_Sigma` on the throat `S2`. Route B is a compact frame/phase direction
paired with `aroundSigma`. Both routes are currently blocked, so the branch
still has no internal `alpha` law.

`ComplexRealityTwoExitEvaluationGate` ranks the two exits. The direct route is
the throat `S2` with an active `Omega_Sigma` area component. The higher-risk
route is `aroundSigma x compact_phase`, which would require a Janus-derived
compact phase/fiber. Topology by itself is not enough: the closed two-cycle
must live in physical boundary phase space and carry a nonzero KKS period.

`ComplexRealityCandidateBoundaryPhaseSpaceGate` constructs the cleanest
mathematical candidate: attach a compact `CP1 ~= SU(2)/U(1)` spinor/frame orbit
to the boundary. Its KKS form is `Omega_j = j sin(theta) dtheta^dphi`, with
period `4*pi*j` and prequantization condition `2*j/hbar in Z`. This answers
what such an object would look like. It does not yet prove that Janus/PT
requires this orbit, nor that `j` maps to `alpha_m`.

See also `docs/janus_complex_reality_candidate_phase_space_matrix.md`.
The core candidate set is restricted to three families: active throat `S2`,
`CP1` spinor/frame orbit, and `aroundSigma x compact phase`. Extensions such
as Moebius, Klein, Pin/spin lift, TQFT level or larger `CPn` are only useful if
they produce one of those three mechanisms with nonzero KKS period.

`ComplexRealityQuantumCandidateWorkbenchGate` plugs the three candidates into
the previous quantum frontier. The result is not a prediction of `alpha`; it is
a ranking of quantum viability. `CP1` gives the cleanest finite Hilbert-space
candidate, active throat `S2` remains the direct geometric route, and
`aroundSigma x phase` still needs a derived compact phase.

`ComplexRealityCombinedPhaseSpaceCandidateGate` keeps the three candidates for
later and starts with their combination:
`S2 throat support + CP1 quantum fiber + aroundSigma holonomy constraint`.
This is coherent, but not closed. The next concrete object is the action of
`aroundSigma` on the `CP1` fiber.

The first derivation pass closes the status sharply. `CP1` is mathematically
available from a local boundary spinor line, but not globally Janus/PT-derived.
The `aroundSigma` action is classified: the central lift is trivial on `CP1`,
while a useful noncentral projective action would need a derived spin/Pin
holonomy. The combined KKS period is symbolically nonzero if `j != 0`, but the
Janus-derived nonzero period is still blocked by missing sector selection.

The active hypothesis is:

`X2026-complex-reality` may supply the missing Souriau/coadjoint machinery for
the previous `alpha` blockage, but only if it yields a nonzero symplectic/KKS
density and an integrality law.

`ComplexRealityPrequantizationIntegralityGate` and
`ComplexRealityAlphaStateLawVerdictGate` close the current pass. The branch has
a sourced complex coadjoint scaffold and a symbolic KKS candidate, but it still
does not provide a closed quantizable boundary cycle, a nonzero normalized KKS
period, a mass/charge lattice, a primitive sector law, or a map to `alpha_m`.

Current verdict: `branch_status = frozen_pending_state_law`.
`alpha_generated_now = false`.
