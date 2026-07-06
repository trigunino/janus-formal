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
  - `metric_tetrad_component`: `delta h_ab` parity closed as even, but
    `R_h_ab` must still be proved Z2-odd. This follows conditionally if
    `tau_Z2^* L_ct = -L_ct`.
  - `extrinsic_tetrad_component`: `delta K_ab` parity closed as odd, but
    `R_K_ab` must still be proved Z2-even. This follows conditionally if
    `tau_Z2^* L_ct = -L_ct`.
  - `matter_flux_channel = false`
  - `stress_tensor_channel = false`
  - `spinor_current_channel = true` for the residual channel because
    `R_psi=R_psibar=0` is emitted locally; global Dirac current parity remains
    separate.
  - `paired_sheet_residual_support = true` from the projective two-fold tunnel
    cover with Sigma throat support. This does not prove matter-flux
    equivariance or component parity.

Important: `E_counterterm = 0` is not required by the active model. It is only
the Z2 quotient-cancellation bypass. If `tau_Z2^* L_ct = -L_ct` fails, the
correct route is a derived nonzero `E_counterterm(a)`.

`tau_Z2^* L_ct = -L_ct` is also not an independent shortcut in the current
chain. From `L_ct = -integral alpha_res`, it follows only after
`alpha_res` anti-invariance is already proved. Therefore using `L_ct` oddness
to prove the tetrad pieces of `alpha_res` is circular.

Toy exact finite-throat diagnostic:

- `h_ab=R^2 q_ab`
- `K_ab^+=+R q_ab`, `K_ab^-=-R q_ab`
- linear `K` terms are Z2-odd
- `K^2` and intrinsic-curvature terms are Z2-even
- point-collapse power-law integrals vanish in the toy limit `R -> 0`

This is useful to reject false symmetry claims, but it is not an active proof of
the Sigma counterterm.

Minimal torsionless finite-throat density basis diagnostic:

`L_ct^min = c1*(epsilon_Z2 K) + c2*K^2 + c3*R[h]`

- constant term removed by zero-throat normalization
- torsion term removed on active torsionless branch
- Immirzi/radion gradient excluded until full `R_chi` parity exists
- symmetry gives only the basis, not the coefficients
- missing constraints: metric residual trace and extrinsic residual trace

Minimal-basis trace diagnostic:

- `sqrt(h)L_min = sqrt(q)*(3*c1*epsilon_Z2*R^2 + (9*c2+6*c3)*R)`
- `E_counterterm = sqrt(q)*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)`
- even the strong toy condition `E_counterterm=0` for all `R` leaves
  `c1=0`, `3*c2+2*c3=0`, with one free coefficient
- active `R_h_trace` and `R_K_trace` are still the required non-circular inputs

Dual-route decision:

- active trace solution route: blocked, no active `R_h_trace/R_K_trace` payload
- nonzero route: parametric only,
  `E_ct(R)=sqrt(q)*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)`
- no numeric `E_counterterm(a)` until `c1,c2,c3`, `R_Sigma(a)` and volume
  normalization are derived
- no `E_counterterm=0` claim and no coefficient fitting

Resolved throat boundary trace target:

- `Sigma` is treated as the geometric Z2 tunnel throat/interface, not a
  numerical boundary.
- The active boundary condition is
  `tau_Z2^* h_ab = h_ab`, `tau_Z2^* n = -n`,
  `tau_Z2^* K_ab = -K_ab`, stationary throat, no free boundary stress.
- This supports the `R_Sigma_solution_certificate` route and identifies the
  missing trace targets, but does not emit them:
  `R_h_trace_derived = false`, `R_K_trace_derived = false`.
- Next non-circular input remains the local variation of the full Sigma
  boundary action, or an equivalent derived junction/stationarity equation,
  producing `R_h_trace` and `R_K_trace`.

Resolved throat trace equations:

- The finite Z2 throat gives the Israel trace target
  `S = h^ab S_ab = 12/(kappa_Z2Sigma R)` on the round throat branch.
- The minimal constant basis gives
  `R_K_q = -3*(c1*epsilon_Z2 + 6*c2/R)/R^2`
  and
  `h_trace_R_h = 3*c1*epsilon_Z2/R + (18*c2+6*c3)/R^2`.
- If the ensemble is Dirichlet in `h` only and imposes no independent
  `K` variation, `R_K_q=0` forces `c1=0`, `c2=0`, leaving
  `h_trace_R_h=6*c3/R^2`.
- That scaling cannot match the finite-throat Israel stress trace `~1/R` for
  all `R` with constant `c3`.
- Therefore the minimal constant basis does not close the active finite-throat
  counterterm. The next real branch is either a mixed `h,K` boundary ensemble
  with a derived `R_K_trace`, or a non-minimal/local density derived from the
  bulk/tunnel resolution.

Mixed `h,K` trace solution:

- If independent `K` variation is allowed, the minimal basis can match the
  finite-throat trace scaling only with
  `c1 = 4 epsilon_Z2/kappa_Z2Sigma` and `c3 = -3 c2`.
- This necessarily activates the linear term `c1 epsilon_Z2 K`.
- That term is Cartan-GHY-like. As an independent `L_ct`, it violates the
  active non-duplication policy for the counterterm.
- Therefore the minimal mixed `h,K` counterterm is not promoted. The linear
  `K` contribution must be assigned to the existing Cartan-GHY/junction block,
  or the residual counterterm must come from a genuinely non-GHY local density
  derived from the tunnel resolution.

Linear `K` partition audit:

- The finite-throat trace match asks for the same operator class
  `sqrt(|h|) K` already carried by the Cartan-GHY boundary block.
- Therefore a linear `K` term cannot remain in the independent counterterm
  basis.
- The next check is a Cartan-GHY + junction normalization audit against the
  finite-throat trace. Any residual counterterm after subtracting the known
  `sqrt(|h|)K` operator must be genuinely non-GHY.

Cartan-GHY + junction trace partition:

- On the round finite Z2 throat,
  `[K_ab - K h_ab] = -4 R q_ab` and
  `h^ab [K_ab - K h_ab] = -12/R`.
- The Lanczos-Israel equation gives
  `S_ab = 4 R q_ab/kappa_Z2Sigma`, hence
  `S = 12/(kappa_Z2Sigma R)`.
- This exactly accounts for the finite-throat linear `K` trace through the
  existing Cartan-GHY/junction operator.
- Therefore the independent counterterm has
  `linear_K_counterterm_residual_after_partition = 0` and
  `c1 = 0` after partition.
- This does not close the full counterterm: any remaining `L_ct` must be
  genuinely non-GHY, or it must be proved absent.

Remaining non-GHY channel audit:

- Closed/zero after partition:
  linear `K` GHY channel, torsion pullback channel, radial Immirzi contraction.
- Still open:
  metric non-GHY trace `R_h`, extrinsic non-GHY trace `R_K`, full nonradial
  Immirzi residual, and residual connection/embedding/matter channels.
- Therefore `E_counterterm=0` is still not proved. Missing channels are not
  allowed to be treated as zero.

Non-GHY absence readiness:

- The known partition is clean, but proving absence of the remaining non-GHY
  channels requires the active first action to be fully assembled.
- Current active first-action blockers:
  plus/minus Dirac matter actions, cross-transport source acceptance, and final
  action assembly. The local torsionless coframe/connection pullback is now
  consumed by the Dirac reduction path; the remaining Dirac blocker is
  global `plus_spinor_data_ready` / resolved-tunnel spinor projection. The
  local projected counterterm spinor residual channel is already closed.
- Therefore `E_counterterm=0` cannot be promoted from counterterm algebra alone.

Spinor residual refinement:

- The local MIT/Z2 reflecting projector algebra is available on Sigma:
  `local_MIT_reflecting_projector_ready = true` and
  `normal_current_zero_algebra_ready = true`.
- The phase-fixed self-adjoint reflecting boundary condition is now derived
  locally from the Sigma boundary variational package:
  `local_reflecting_boundary_condition_derived = true`.
- The local leakage/current channel is therefore closed:
  `local_normal_dirac_current_zero_ready = true`.
- This still does not close the projected/global spinor channel:
  `global_Z2Sigma_spinor_projection_ready = false`.
- The local spinor projection map is now separated from the global one:
  `local_Z2Sigma_spinor_projection_ready = true`, but
  `Z2Sigma_spinor_projection_ready = false`.
- The local projected spinor residual coefficients are now explicit:
  `R_psi = 0`, `R_psibar = 0` in the local Sigma reflecting projected
  variation.
- The counterterm spinor residual channel is closed locally:
  `counterterm_spinor_residual_channel_ready = true`.
- This does not claim a global resolved-tunnel spinor bundle.

Round-throat tensor reduction:

- The active Sigma/RP3 throat has a unit intrinsic metric
  `q_ab = diag(1,1,1)` in the active projective orthonormal chart.
- By round-throat isotropy, the open metric/extrinsic counterterm residual
  tensors reduce to scalar traces:
  `R_h^{ab} = (R_h_trace/d) q^{ab}` and
  `R_K^{ab} = (R_K_trace/d) q^{ab}`.
- The repo now has a trace-to-tensor writer:
  `scripts/build_p0_eft_janus_z2_sigma_counterterm_trace_residual_tensor_input_writer_gate.py`.
- The remaining physical input is therefore
  `outputs/active_z2_sigma/counterterm_trace_residual_inputs.json` with
  `a_grid`, `R_h_trace_values`, and `R_K_trace_values`.
- This reduces tensor shape freedom only. It does not derive the two scalar
  traces and does not prove `E_counterterm=0`.
