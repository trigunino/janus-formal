# Janus Alpha Superselection Sector Program

## Interpretation

`alpha` is treated as a global state-sector label of the Janus exact solution.

It is not a local fitted coupling and not a topology-only prediction.

Analogy: an ADM mass or conserved charge labels a solution sector. Observations
identify which sector describes our universe.

## Contract

- `alpha_is_global_state_sector = true`
- `alpha_is_local_fit_parameter = false`
- `alpha_is_topology_prediction = false`
- `full_no_fit_prediction = false`
- `observational_sector_selection = allowed`

## Observation Order

1. SN: tests shape/q0 branch, but not absolute alpha scale alone.
2. BAO: required for absolute ruler/scale breaking if a native ruler contract is
   declared.
3. H(z): optional expansion-rate cross-check.
4. CMB: later only after native background and ruler closure.

## Allowed Claim

Janus can be evaluated as a family of alpha sectors, with observations selecting
or constraining the sector of our universe.

## Forbidden Claim

The current model does not predict `alpha` no-fit.

## Current Endpoint Status

Local JLA/SN files are sufficient for a shape-only/q0-sector check.

Full alpha-sector selection requires BAO/ruler data because SN alone does not
break the absolute scale degeneracy.

## Current Observation Closure

DESI DR2 BAO data are available through `data/external/bao_data`.

The current SN full-covariance + BAO runner selects the `q0 -> 0-` boundary,
not an interior Janus sector, with the present background-proxy BAO map.

Closure status:

`superselection_calibration_closes_negative_for_current_background_proxy`.

Reopen only after deriving a native Janus BAO/ruler contract.
