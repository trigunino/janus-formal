# Janus Bridge State Law

## Core Idea

Treat `alpha` as a bridge-state charge:

```text
bridge state -> chi_LL -> R_s -> M_bridge -> alpha -> observables
```

This reframes the problem. Janus is not only bulk bimetric geometry. A complete
model needs a state law on the Sigma/PT bridge.

## Rules

- no direct alpha fit;
- no invented Sigma density;
- no legacy Z4 shortcut;
- observations rank sectors only after an internal state law is defined.

## Candidate Routes

1. `null_boundary_noether_charge`
   - geometric boundary charge route;
   - needs active null boundary phase space and generator normalization.

2. `LL_worldvolume_flux_sector`
   - microscopic tension route;
   - needs `q_LL`, `F2_0`, compact cycle, and primitive sector.

3. `PT_minimal_quantum_state`
   - quantum-state route;
   - needs state space, charge operator, and minimal nonzero-sector theorem.

## Current Status

Opened, not closed.

`chi_LL_selected_no_fit = false`.

## Discriminator

No single route is sufficient alone.

Current non-rustine path:

1. derive `Q_bridge` from the null/PT boundary symplectic structure;
2. derive a `chi_LL` flux/tension lattice from the LL worldvolume sector;
3. derive PT primitive nonzero state selection;
4. map `Q_bridge/chi_LL -> M_bridge -> alpha -> background`.

Status: composite path declared, not closed.

## Terminal Pistes Verdict

The credible routes are now classified:

1. `composite_boundary_state_law`
   - credible no-fit route;
   - blocked until an explicit active boundary phase space/action supplies
     `Q_bridge`, LL flux/tension units, and PT primitive-sector selection.

2. `alpha_superselection_sector`
   - viable non-no-fit contract;
   - `alpha` is treated like a global state label, comparable in role to an ADM
     mass sector;
   - observations may select the sector, but this must not be called no-fit.

3. `paper_reference_gap_report`
   - useful formal output;
   - freezes what the published Janus source set fixes and what it leaves open.

Decision: without a derived boundary state law, the honest next program is
sector calibration plus a paper-reference gap report.
