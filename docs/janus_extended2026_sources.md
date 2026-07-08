# Janus Extended2026 Source Set

This file defines the post-2024 source bundle that can support an
`extended2026` branch, without mixing it into the strict `paper_only` 2024
reference.

For the broader 2025-2026 public source landscape, including compact-object and
controversy documents, see `docs/janus_2026_public_source_index.md`.
For a short human synthesis of what the 2026 family adds and does not add, see
`docs/janus_2026_source_analysis.md`.

## Scope

`extended2026` is broader than `paper_only`, but it is not a dump of every
Janus-adjacent PDF. It is split into four layers so the active cosmology branch
stays readable.

## Layer 1: core_active

These are the active sources for actual `extended2026` background work.

1. `EPJC2024_the-janus-cosmological-model.pdf`
   - local: `data/raw/janus_library/EPJC2024_the-janus-cosmological-model.pdf`
   - role: published baseline reference.

2. `M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
   - local: `data/raw/janus_library/M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
   - role: cited SN comparison machinery (`q0=-0.087`, exact-shape proxy, magnitude-redshift relation).

3. `X2025-bimetric-hal_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
   - local: `data/raw/janus_library/X2025-bimetric-hal_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
   - role: HAL mirror of the 2024 bimetric paper; mirror/check, not new physics by itself.

4. `X2025-technical-book_the-janus-cosmological-model.pdf`
   - local: `data/raw/janus_library/X2025-technical-book_the-janus-cosmological-model.pdf`
   - role: long technical synthesis/context; useful for cross-checks and formula lookup.

5. `X2026-expansion-desi_janus-exact-expansion-solution-and-desi.pdf`
   - local: `data/raw/janus_library/X2026-expansion-desi_janus-exact-expansion-solution-and-desi.pdf`
   - role: post-2024 expansion/observation extension focused on DESI.

6. `X2026-variable-constants_alternative-to-inflation-variable-constants-regime.pdf`
   - local: `data/raw/janus_library/X2026-variable-constants_alternative-to-inflation-variable-constants-regime.pdf`
   - role: post-2024 early-universe / variable-constants extension.

## Layer 2: supporting_cosmology

These are part of the `extended2026` evidence bundle, but they remain support
material rather than active executable anchors.

1. `X2022-hal-acceleration-cosmic-expansion`
   - role: historical bridge to the later DESI-era expansion claim.

2. `C2015-cosmic-acceleration-reinterpretation`
   - role: earlier exact-solution SN reinterpretation.

3. `C2017-janus-forty-years`
   - role: long-form synthesis before the 2024 publication cycle.

4. `C2021-janus-antimatter-synthesis`
   - role: broad Janus synthesis between older negative-mass rhetoric and the modern bimetric branch.

5. `C2021-janus-radiative-era`
   - role: radiative-era / early-universe precursor to the 2026 variable-constants branch.

6. `C2024-janus-consistent-hal`
   - role: consistency synthesis, useful for checking later 2024/2025 wording against the published core.

## Layer 3: supporting_math

These matter for formal interpretation, not direct background execution.

1. `M31`
   - role: published symmetry layer.

2. `X2025-symplectic-hal`
   - role: HAL mirror/check of the symmetry layer.

3. `C2014-sakharov-meaning`
   - role: earlier Sakharov / twin-universe interpretation bridge.

## Layer 4: adjacent_noncore

Indexed and kept available, but not imported into the cosmology/background
branch unless a concrete bridge is derived.

- `C2014-negmass-gr`
- `C2014-negmass-paradox`
- `C2014-neggrav-lensing`
- `C2014-spiral-structure`
- `C2014-vls-compact-space`
- `C2021-dipole-repeller`
- `C2021-janus-crisis-fr`
- `X2025-rebuttal-damour`
- `X2025-modele-janus-impasse`
- `X2025-kinetic-galactic`
- `X2025-plugstars-jmp`
- `X2026-questionable-black-holes`
- `X2026-black-hole-inconsistency-I`
- `X2026-black-hole-analytic-extension`
- `X2026-black-hole-inconsistency-II`
- `X2026-complex-reality`

## Reading order

For actual branch construction:

1. 2024 baseline: `EPJC2024`
2. cited comparison layer: `M18`
3. cosmology mirror/sanity layer: `X2025-bimetric-hal`
4. long synthesis/context: `X2025-technical-book`
5. observational extension: `X2026-expansion-desi`
6. early-universe extension: `X2026-variable-constants`
7. only then supporting precursors (`C2015`, `C2021`, `C2024`) for cross-checks
8. use symmetry texts (`M31`, `X2025-symplectic-hal`) only when needed by the formal branch

## Policy

- `paper_only` stays frozen and strict.
- `paper_plus_cited_comparison` stays separate.
- `extended2026` is a third class: a post-2024 extension bundle, not paper-only evidence.
- only `core_active` should drive executable background work by default.
