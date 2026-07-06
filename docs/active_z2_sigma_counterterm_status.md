# Active Z2/Sigma Counterterm Status

## Closed

- Boundary action:
  `S_ct[Sigma] = integral_Sigma d^3y sqrt_abs_h L_ct(h_ab,K_ab,T_pullback_A,chi,epsilon_Z2)`.
- Boundary measure:
  `dmu_Sigma = d^3y sqrt_abs_h`.
- Non-duplication policy:
  not Cartan-GHY, not Holst/Nieh-Yan-only, not matter/dust action, not tunnel junction.
- Variation formula:
  `R_h_ab = -(1/2 h^ab L_ct + partial L_ct/partial h_ab)`.
  `R_K_ab = -partial L_ct/partial K_ab`.
  `R_chi = -partial L_ct/partial chi`.
- Partial active torsionless closures:
  `R_T^A = 0`.
  `R_chi partial_R chi = 0`.

## Active Blocker

The nonlinear Sigma closure now emits a component schema but not component
values:

- `alpha_res_components_available = true`
- `alpha_res_component_decomposition_available = true`
- `alpha_res_component_values_available = false`
- `R_h_ab_emitted = false`
- `R_K_ab_emitted = false`
- `R_chi_emitted = false`
- `L_ct_expression_emitted = false`

Therefore the model cannot yet write:

- `counterterm_local_density_action_inputs.json`
- `counterterm_metric_residual_tensor_inputs.json`
- `counterterm_extrinsic_residual_tensor_inputs.json`
- `counterterm_lct_radial_profile.json`
- `rsigma_E_counterterm.json`

## Current Artifacts

- `counterterm_alpha_res_partial.json`
- `counterterm_immirzi_residual_scalar_inputs.json`
- `counterterm_lct_expression_obstruction.json`
- `counterterm_local_density_action_obstruction.json`
- `counterterm_radial_geometry_factors.json`
- `counterterm_radial_projection_formula.json`
- `counterterm_residual_coefficients_partial.json`
- `counterterm_symbolic_local_primitive.json`
- `counterterm_tetrad_transport_closure.json`

## Next Physical Target

Refine `P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate` from boolean
cancellation/uniqueness into component-value emission:

- emit explicit `alpha_res_component_values`, or
- emit explicit `L_ct_expression`, or
- emit `R_h_ab`, `R_K_ab`, `R_chi`.

No downstream counterterm radial closure is allowed before this.

## Outside-Box Z2 Route

A possible bypass exists only if the residual one-form is odd under the Janus
sheet exchange:

`tau_Z2^* alpha_res = - alpha_res`.

Then the quotient projection could cancel the Sigma residual and give
`E_counterterm = 0` without constructing `L_ct`.

Current status:

- Z2 normal orientation reversal is available.
- The torsionless Holst boundary flux slot is available.
- The `alpha_res` component schema is available.
- The anti-invariance of `alpha_res` is not proved.
- Route status: `credible_but_blocked`.
- Primary blocker: `componentwise_parity_proofs`.
- Open channel tests:
  - `all_emitted_components_odd = false`
  - `matter_flux_channel = false`
  - `stress_tensor_channel = false`
  - `spinor_current_channel = false`
  - `paired_sheet_residual_support = false`
