# Janus 2025-2026 Public Source Index

This file is the practical index for the post-2024 Janus source family.

It is intentionally broader than `docs/janus_extended2026_sources.md`.

Use it to answer a simple question:

What do we actually have locally for the 2025-2026 Janus ecosystem, and what
role should each source play in the repo?

## Families

### 1. Cosmology core

These are the sources that matter first for background-expansion and observable
reproduction work.

| ID | Year | Title | Intended role |
|---|---:|---|---|
| `M30` | 2024 | A bimetric cosmological model based on Andrei Sakharov's twin-universe approach | published baseline equations |
| `M18` | 2018 | Constraints on Janus Cosmological model from recent observations of supernovae type Ia | published SN comparison layer |
| `X2025-bimetric-hal` | 2025 | HAL mirror of the bimetric paper | mirror / checksum, not new physics |
| `X2025-technical-book` | 2025 | The Janus Cosmological Model | long synthesis and equation lookup aid |
| `X2026-expansion-desi` | 2026 | Janus exact expansion solution and DESI | post-2024 expansion claim |
| `X2026-variable-constants` | 2026 | Alternative to Inflation: Variable Constants Regime | early-universe / ruler calibration extension |

### 1b. Cosmology precursor

Useful antecedent to the post-2024 branch, but not part of the strict 2024
paper-only reference.

| ID | Year | Title | Intended role |
|---|---:|---|---|
| `X2022-hal-acceleration-cosmic-expansion` | 2022 | Janus, the only cosmological model that explains the acceleration of cosmic expansion | precursor expansion document / historical bridge |

### 2. Symmetry and mathematical extension

These inform the formal side, but they do not by themselves close the
cosmological observable path.

| ID | Year | Title | Intended role |
|---|---:|---|---|
| `M31` | 2024 | Study of symmetries through the action on torsors of the Janus symplectic group | published symmetry layer |
| `X2025-symplectic-hal` | 2025 | HAL mirror of the Janus symplectic group paper | mirror / equation lookup |
| `X2026-complex-reality` | 2026 | The Real World as a part of a Complex Reality | speculative extension, not core evidence |

### 3. Compact-object branch

These belong to a separate family. They should not be mixed into the
cosmology/background branch unless a concrete bridge is derived.

| ID | Year | Title | Intended role |
|---|---:|---|---|
| `X2025-plugstars-jmp` | 2025 | Alternatives to Black Holes: Gravastars and Plugstars | published compact-object branch |
| `X2026-questionable-black-holes` | 2026 | Questionable Black Holes | author-side compact-object critique |
| `X2026-black-hole-analytic-extension` | 2026 | The black hole model goes with an analytic extension of spacetime | compact-object continuation |
| `X2026-black-hole-inconsistency-I` | 2026 | Mathematical and Geometrical Inconsistency of the Black Hole Model. Part I | compact-object critique |
| `X2026-black-hole-inconsistency-II` | 2026 | Mathematical and Geometrical Inconsistency of the Black Hole Model. Part II | compact-object critique |

### 4. Transitional / controversy documents

These can matter for chronology and source provenance, but should not be
promoted automatically into the physical core.

| ID | Year | Title | Intended role |
|---|---:|---|---|
| `X2025-rebuttal-damour` | 2025 | Rebuttal of Damour's criticism of the Janus model | controversy/provenance |
| `X2025-modele-janus-impasse` | 2025 | Modele Janus Impasse | self-diagnostic / transition text |

## Policy

1. `paper_only` stays strict and untouched.
2. `paper_plus_cited_comparison` stays separate.
3. `extended2026` should use the cosmology core first.
4. Compact-object and controversy texts are indexed, but not imported as
   cosmology evidence by default.

## Practical next use

If the goal is observational reproduction:

1. start with `M30`, `M18`, `X2026-expansion-desi`, `X2026-variable-constants`;
2. use `X2025-technical-book` and the HAL mirrors only as navigation and
   cross-check layers;
3. keep compact-object texts in their own branch family.
