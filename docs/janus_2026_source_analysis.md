# Janus 2026 Source Analysis

This note summarizes what the local 2025-2026 Janus source set gives us, and
what it still does not give us.

## Inventory status

The local Janus library now includes:

- the historical map corpus (`M01` to `M31`);
- the 2022 HAL precursor around cosmic acceleration;
- the 2025-2026 public add-on corpus (`X2025-*`, `X2026-*`);
- machine keyword index;
- source cards;
- knowledge-base coverage.

See:

- `docs/janus_bibliography.md`
- `docs/janus_2026_public_source_index.md`
- `outputs/reports/p0_eft_janus_extended2026_core_status.json`
- `outputs/reports/janus_library_keyword_index.md`
- `docs/janus_knowledge_base.md`

## What matters most for cosmology

If the goal is to reconstruct the Janus background/observation path, the useful
core is still small:

1. `M30`
   - published bimetric cosmology baseline.
2. `M18`
   - published supernova comparison layer.
3. `X2026-expansion-desi`
   - post-2024 claim that the Janus exact expansion law aligns with DESI-era
     dark-energy hints.
4. `X2026-variable-constants`
   - post-2024 early-universe extension, useful for ruler/horizon discussion.
5. `X2025-technical-book`
   - long lookup/synthesis layer, useful for tracing formulas and prose
     continuity, but not automatically equal to a published executable model.

## What the 2026 sources add

### `X2026-expansion-desi`

Adds:

- a stronger observational claim around DESI;
- a renewed emphasis on the exact Janus expansion route;
- a direct bridge between published Janus background equations and post-2024
  expansion rhetoric.

Does not add by itself:

- an executable BAO ruler derivation;
- a full native observable pipeline;
- an absolute density normalization if the older equations leave it open.

### `X2026-variable-constants`

Adds:

- a post-2024 variable-constants branch;
- a candidate explanation for horizon/ruler problems without inflation;
- a useful clue for how Janus wants to treat early scales.

Does not add by itself:

- a direct, code-ready CMB prediction pipeline;
- a verified BAO observable formula;
- a full background normalization contract.

### Compact-object 2026 family

- `X2026-questionable-black-holes`
- `X2026-black-hole-inconsistency-I`
- `X2026-black-hole-inconsistency-II`
- `X2026-black-hole-analytic-extension`

These enrich the compact-object branch, but they do not solve the cosmological
background problem directly.

### `X2026-complex-reality`

This is useful as a speculative or philosophical extension. It should remain
outside the evidentiary core for cosmology until a concrete mathematical bridge
to observables is extracted.

## What the 2025 transition texts add

### `X2025-rebuttal-damour`

Useful for:

- chronology;
- understanding what Janus authors consider the core objections;
- tracing how the 2024-2026 presentation hardened.

Not sufficient as a direct observational source.

### `X2025-modele-janus-impasse`

Useful for:

- self-diagnostic context;
- understanding internal transition points in the Janus narrative.

Not a replacement for the published cosmology equations.

## Bottom line

After indexing the 2025-2026 corpus, the repo is in a better source state:

- we do have the 2026 public source family locally;
- we do have machine navigation over it;
- we do have a clean separation between cosmology core and side branches.

But the scientific blocker remains the same:

the 2026 source family strengthens the Janus narrative, yet still does not
automatically provide a complete native observable contract from the bimetric
equations to SN + BAO + CMB without additional derivation work.
