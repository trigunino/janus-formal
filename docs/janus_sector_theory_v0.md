# Janus Sector Theory v0

## Purpose

This branch tests a pragmatic idea: if `alpha` is a global sector label rather
than a locally predicted constant, the model can still be confronted with data
without pretending this is a no-fit prediction.

## Rules

- No direct fit of `alpha`.
- No hidden physical law inserted as true.
- SN offset and BAO scale may be profiled as observational nuisances.
- A `q0` grid is interpreted as sector selection, not a no-fit derivation.

## Current Result

Routes that try to generate `alpha` internally remain blocked. The only live
testable route is observational sector selection.

Existing SN+BAO machinery currently classifies the endpoint as moving toward a
GR-like boundary, not toward the published `q0=-0.087` sector.

## Status

`no_fit_alpha_generated = false`.

This branch is useful for falsification/ranking of sectors. It is not a closed
Janus state law.
