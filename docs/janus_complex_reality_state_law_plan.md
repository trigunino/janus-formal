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

Lean formalization is now present in `JanusFormal.ComplexRealityStateLaw`.
It imports the source curation, Eq. 131 projection, coadjoint state-space,
KKS boundary-density, and Sigma boundary-projection gates. The formal status
matches the scripts: symbolic branch ready, active density and `alpha`
generation still blocked.

The active hypothesis is:

`X2026-complex-reality` may supply the missing Souriau/coadjoint machinery for
the previous `alpha` blockage, but only if it yields a nonzero symplectic/KKS
density and an integrality law.
