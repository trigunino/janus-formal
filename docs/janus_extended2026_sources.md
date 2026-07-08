# Janus Extended2026 Source Set

This file defines the post-2024 source bundle that can support an `extended2026`
branch, without mixing it into the strict `paper_only` 2024 reference.

For the broader 2025-2026 public source landscape, including compact-object and
controversy documents, see `docs/janus_2026_public_source_index.md`.
For a short human synthesis of what the 2026 family adds and does not add, see
`docs/janus_2026_source_analysis.md`.

## Scope

`extended2026` is the smallest coherent extension beyond the 2024 published paper
for cosmology/background work.

Included:

1. `EPJC2024_the-janus-cosmological-model.pdf`
   - local: `data/raw/janus_library/EPJC2024_the-janus-cosmological-model.pdf`
   - role: published baseline reference.

2. `X2025-bimetric-hal_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
   - local: `data/raw/janus_library/X2025-bimetric-hal_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
   - role: HAL mirror of the 2024 bimetric paper; useful as mirror/check, not a new physical layer by itself.

3. `X2025-symplectic-hal_study-of-symmetries-through-the-action-on-torsors-of-the-janus-symplectic-group.pdf`
   - local: `data/raw/janus_library/X2025-symplectic-hal_study-of-symmetries-through-the-action-on-torsors-of-the-janus-symplectic-group.pdf`
   - role: post-2024 symmetry/symplectic extension.

4. `X2025-technical-book_the-janus-cosmological-model.pdf`
   - local: `data/raw/janus_library/X2025-technical-book_the-janus-cosmological-model.pdf`
   - role: long technical synthesis/context; useful for cross-checks and narrative continuity.

5. `M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
   - local: `data/raw/janus_library/M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
   - role: cited SN comparison machinery (`q0=-0.087`, exact-shape proxy, magnitude-redshift relation).

6. `X2026-expansion-desi_janus-exact-expansion-solution-and-desi.pdf`
   - local: `data/raw/janus_library/X2026-expansion-desi_janus-exact-expansion-solution-and-desi.pdf`
   - role: post-2024 expansion/observation extension focused on DESI.

7. `X2026-variable-constants_alternative-to-inflation-variable-constants-regime.pdf`
   - local: `data/raw/janus_library/X2026-variable-constants_alternative-to-inflation-variable-constants-regime.pdf`
   - role: post-2024 early-universe / variable-constants extension.

## Deliberately excluded from extended2026 core

Excluded for now because they are not central to the cosmology/background branch:

- compact-object / black-hole challenge papers;
- plugstar / galactic kinetic papers;
- broader philosophical or “complex reality” texts.

These can be added later as separate extension families if needed.

## Reading order

For actual branch construction:

1. 2024 baseline: `EPJC2024`
2. cited comparison layer: `M18`
3. symmetry extension: `X2025-symplectic-hal`
4. cosmology mirror/sanity layer: `X2025-bimetric-hal`
5. long synthesis/context: `X2025-technical-book`
6. observational extension: `X2026-expansion-desi`
7. early-universe extension: `X2026-variable-constants`

## Policy

- `paper_only` stays frozen and strict.
- `paper_plus_cited_comparison` stays separate.
- `extended2026` is a third class: a post-2024 extension bundle, not paper-only evidence.
