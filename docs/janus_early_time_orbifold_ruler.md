# Janus Early-Time Orbifold Ruler

This branch evaluates four non-rustine routes from Janus/Z2/orbifold structure
to a native BAO ruler.

## Problem

The paper-native late-time branch can define `D_M^J`, `D_H^J`, and `D_V^J`.
BAO also needs a native `r_d^J`.

The current exact normalized branch has:

```text
z_max(q0) = -1 / (2 q0)
```

For `q0 = -0.087`, this gives `z_max ~= 5.747`, not a pre-drag domain.

## Routes

| Route | Meaning | Current status |
| --- | --- | --- |
| Orbifold redshift map | derive `z_obs = F_orbifold(z_global)` | blocked: no derived transport map |
| Early-time sister branch | derive a separate pre-drag branch matched to the late branch | blocked: no matching law or pre-drag `H_J` |
| Topological spectrum ruler | derive `r_d^J` from a Sigma/orbifold eigenlength | blocked: no absolute scale or plasma coupling |
| Projected photon-baryon plasma | derive `c_s^J`, `Gamma_drag^J`, `z_d^J`, `H_J` | blocked: active primitives missing |

## Ranking

1. Projected photon-baryon plasma.
2. Early-time sister branch.
3. Orbifold redshift map.
4. Topological spectrum ruler.

Topology matters only if it supplies a physical map, matching law, spectrum with
scale, or plasma projection. Topology alone does not produce `r_d^J`.

## Projected plasma frontier

The projected photon-baryon plasma route has now been pushed to the current
non-rustine bottom.

Already calculable:

- conserved baryon/photon histories after active normalizations;
- `c_s^J` from `rho_b^J` and `rho_gamma^J`;
- Saha/free-electron/Thomson drag machinery;
- `z_d^J` from `Gamma_drag^J = H_J`;
- `r_d^J = integral c_s^J/H_J dz`.

Still blocked:

- no active `early_plasma.json`;
- no active `background_H0_inputs.json`;
- no derived active baryon number density on `Z2/Sigma`;
- no derived active photon/baryon normalization from the paper-native branch;
- no pre-drag `E_J(z)` / `H_J(z)`.

Report:

```text
outputs/reports/p0_eft_janus_projected_photon_baryon_plasma_frontier_gate.md
```

Generated report:

```text
outputs/reports/p0_eft_janus_early_time_orbifold_ruler_closure_gate.md
```
