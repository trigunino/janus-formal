# Janus 2024 Reference Branch Sources

This file indexes the concrete source set used for the two 2024 reference classes.

## paper_only

Active branch class. Only paper-explicit content counts.

Primary sources:

- `EPJC2024_the-janus-cosmological-model.pdf`
  - local: `data/raw/janus_library/EPJC2024_the-janus-cosmological-model.pdf`
  - role: published 2024 paper-native bulk equations, `x0` common-time FLRW object,
    `k = kbar = -1` branch, global energy equation shape, sector dust-density laws,
    observational anchor statements.

- `M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
  - local: `data/raw/janus_library/M30_a-bimetric-cosmological-model-based-on-andrei-sakharov-s-twin-universe-approach.pdf`
  - role: published relative `5%/95%` sector ratio support used in the repo source map.

Not counted as active paper_only content:

- cited comparison helpers;
- repo calibration wrappers;
- repo bulk-history wrappers.

## paper_plus_cited_comparison

Inactive helper class. Adds cited comparison machinery on top of the paper_only base.

Adds:

- `M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
  - local: `data/raw/janus_library/M18_constraints-on-janus-cosmological-model-from-recent-observations-of-supernovae-t.pdf`
  - role: cited SN comparison paper, `q0 = -0.087`, exact-shape proxy, magnitude-redshift relation.

- `X2025-technical-book_the-janus-cosmological-model.pdf`
  - local: `data/raw/janus_library/X2025-technical-book_the-janus-cosmological-model.pdf`
  - role: local technical-book copy kept as extended context only, not as paper-only evidence.

## Current policy

- `paper_only` remains the active strict reference.
- `paper_plus_cited_comparison` is available for later comparison/reproduction work.
- Neither class currently upgrades to a full executable strict bulk model.
