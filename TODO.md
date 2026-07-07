# TODO - Janus Orbifold Validation

## Current verdict

- Formal topology scaffold: closed.
- Active geometry core: `Z2_tunnel_Sigma`.
- Legacy CMB/Z4 paths: archived diagnostic only.
- Pure math no-axiom closure: closed for the active `Z2_tunnel_Sigma` model.
- Late-time growth / SDSS-eBOSS branch: viable as EFT diagnostic.
- BAO `r_d`: requires a real pre-drag background contraction.
- Archived CMB/Planck: native Z4 gate was executed historically after the
  primordial-imprint lock; those spectra are rejected by Planck and are not
  active model evidence.
- Archived native GR baseline: failed against CAMB shape-only reference, so the
  historical Z4 correction program is archived rather than extended.
- Native GR decomposition: required now; Planck rejection is suspended as a
  physical Janus verdict until an active Z2/Sigma observational model exists.
- Therefore: do not claim full no-fit cosmology yet.
- No-extension frontier: active Z2/Sigma BAO is now blocked by two independent
  open quantities, `R_Sigma` and the absolute projected baryon Noether charge.
  The local `sqrt(R[h])` counterterm can cancel the Cartan/GHY radial block, but
  it leaves `R_Sigma` flat; the Z2-projected Dirac current is conserved, but it
  does not fix the absolute occupation number. Do not choose either by fit.
- Counterterm no-extension update: first-order Holst/Palatini/Nieh-Yan and
  exact boundary/corner channels have now been projected through PT67 and do not
  create an independent local Sigma density. With no published/adopted
  non-topological cross-action, the remaining non-GHY audit proves
  `E_counterterm = 0` under the strict no-extension policy. This writes
  `counterterm_component_inputs.json`, `counterterm_components.json`,
  `flrw_component_inputs_without_matter_flux.json`, `flrw_component_inputs.json`,
  and `flrw_components.json`. The next strict BAO blockers are now
  `background_scalars.json` and `early_plasma.json`, not the counterterm.
- Strict no-extension background verdict: after PT67, the active FLRW component
  manifest exists, but the scale-free background primitive rejects the branch
  because `E_Z2Sigma^2` is not positive on the requested grid. This is a real
  no-rustine stop: the local Sigma/boundary channels reduce to zero and do not
  supply a positive Friedmann source. A physical continuation needs a derived
  dimensionful/state/action input or a published Janus cross-sector source, not
  a fitted replacement density.
- Strict no-extension no-go is now algebraically recorded:
  `E_Z2Sigma(a)^2 = rho_eff(a)/rho_crit0 + omega_k/a^2`; the active no-extension
  PT67 branch has `rho_eff(a)=0`, while the closed projective branch has
  `k_Z2Sigma=+1` and therefore `omega_k<0`. Hence `E^2<0` on the active grid.
  Allowed exits are only a derived positive Friedmann source, a derived non-closed
  spatial branch, or a dimensionful/state/action input that changes the boundary
  Hamiltonian source.
- Boundary-Hamiltonian scalar route: `H0_Z2Sigma`, `R_curv_Z2Sigma_m`, and
  `N_occ` are now classified as boundary/constraint targets, not free source
  densities. `H0_Z2Sigma` must come from the 3+1 projected boundary Hamiltonian
  and lapse/time-gauge normalization; `R_curv_Z2Sigma_m` from Gauss-Codazzi plus
  volume/surface projection; `N_occ` from a spinor/projector state-selection law
  or explicit effective initial-state status. The target gate is
  `build_p0_eft_janus_z2_sigma_boundary_hamiltonian_scalar_targets_gate.py`.
- Scalar target decomposition is now split into three concrete gates:
  `build_p0_eft_janus_z2_sigma_h0_boundary_hamiltonian_projection_gate.py`
  declares the 3+1 ADM/boundary generator route for `H0_Z2Sigma` and blocks on
  active lapse/time-gauge plus on-shell Hamiltonian evaluation;
  `build_p0_eft_janus_z2_sigma_rcurv_gauss_codazzi_projection_gate.py` declares
  the Gauss-Codazzi/volume-surface route for `R_curv_Z2Sigma_m` and blocks on
  the same dimensionful boundary-Hamiltonian scale;
  `build_p0_eft_janus_z2_sigma_nocc_boundary_state_selection_gate.py` declares
  `N_occ` as state/superselection data and blocks on a spinor boundary
  state-selection law or explicit effective-initial-data manifest.
- Hamiltonian-to-Friedmann update: the symbolic map is now fixed,
  `rho_H = Q_boundary/V_eff` then
  `H0^2 = (8*pi*G/3) rho_H - k c^2/R_curv^2`. The numeric H0 route remains
  blocked because the active repo supplies only scale-free ratios, not any of
  the required dimensionful alternatives: absolute `R_Sigma`, boundary/state
  charge, or action scale. This is checked by
  `build_p0_eft_janus_z2_sigma_h0_numeric_input_frontier_gate.py`.
- Brown-York boundary projection contract: Route B is now implemented as a
  strict non-fit input reducer in
  `build_p0_eft_janus_z2_sigma_boundary_projection_charge_contract_gate.py`.
  It accepts `active_z2_sigma_boundary_projection.json` only if it contains
  active `Q_boundary_raw`, same-surface `Q_reference_raw`, `R_Sigma_abs_m`,
  `V_eff_m3`, `kappa_Z2Sigma`, a reference type, and clean provenance. It then
  writes `projected_boundary_charge_inputs.json` for the existing H0 frontier.
  No live input exists yet, so the gate blocks correctly.
- PT67 theta/Brown-York projection exhausted: the active regular PT67 branch now
  projects `theta_HP` and the GHY `DeltaK` channel into a unit-chart boundary
  charge in `build_p0_eft_janus_z2_sigma_boundary_projection_from_theta_pt67_gate.py`.
  Since `DeltaK_s=DeltaK_tau=0` and the Holst/Palatini non-GHY traces vanish,
  `Q_boundary - Q_reference = 0` on the active grid. Therefore route B does not
  supply the positive Friedmann source for the regular PT67 `k=+1` branch.
- PT67 generalized-boundary frontier: standard same-boundary references
  (`Minkowski/Milne`, isometric same-intrinsic-boundary, and Dirichlet
  Brown-York) preserve the PT67 zero. This is now recorded by
  `build_p0_eft_janus_z2_sigma_pt67_generalized_boundary_bc_reference_gate.py`.
  A nonzero PT67 quasilocal charge therefore requires a derived generalized
  boundary-condition/action choice with a well-posed variational principle, not
  a different reference subtraction chosen by hand.
- PT67 generalized-boundary action reduction: the operational density
  `L_B = lambda_0 + lambda_R3 R3 + lambda_K K + lambda_K2 K^2
  + lambda_Kab2 K_ab K^ab` is now reduced by
  `build_p0_eft_janus_z2_sigma_pt67_generalized_boundary_action_reduction_gate.py`.
  If derived coefficients and boundary/reference scalars are supplied, the gate
  computes a symbolic `Q_ren(R_Sigma)`. The live repo has no derived coefficient
  manifest yet, so no numeric `Q_boundary_raw` is emitted.
- PT67 generalized-BC coefficient solver: under the strict no-extension policy,
  `build_p0_eft_janus_z2_sigma_pt67_generalized_bc_coefficient_solver_gate.py`
  fixes all generalized BC coefficients to zero. The linear `K` channel is a
  forbidden Cartan/GHY duplicate and the remaining non-GHY residual channels are
  proved absent. Therefore generalized BCs do not reopen PT67 unless a genuinely
  new, published/adopted boundary action is admitted.
- Noether Hamiltonian boundary update: the boundary charge kind is now fixed as
  `Hamiltonian_boundary_energy` via the covariant phase-space formula
  `delta H_xi = integral_Sigma(delta Q_xi - i_xi theta)` and its Brown-York
  Dirichlet reduction. Numeric closure still requires the absolute surface
  measure or `R_Sigma`, plus active boundary lapse normalization.
- Boundary lapse update: the signed cover time and unit Sigma frame fix the
  local dimensionless lapse `N_boundary_unit_chart = 1`. They do not fix the
  physical time scale in SI units. Numeric Hamiltonian/H0 still requires the
  absolute surface measure or `R_Sigma` and a physical time/length anchor.
- Boundary surface-measure update: the active unit throat metric and topology
  fix the symbolic measure `Vol_Sigma = 2*pi^2*R_Sigma^3`, and the projective
  geometry fixes `R_Sigma/ell_collar = 1`. The absolute length `R_Sigma` remains
  unproved, so the numeric Brown-York/Noether charge remains blocked.
- Natural scale no-go: CODATA `G`, exact `c`, and `hbar` allow construction of
  the Planck length, but the active Janus/Z2/Sigma action currently has no
  theorem identifying `R_Sigma` or `ell_collar` with that length. Therefore
  `R_Sigma = l_P` is not used in the strict branch.
- Action scale inventory: active `G` fixes units/coupling only; Holst/Nieh-Yan
  is zero on the torsionless Sigma branch; no active Lambda, scalar potential,
  tension, mass parameter, or accepted Sigma counterterm scale is present.
  Therefore the strict action inventory does not select an absolute throat
  length.
- Schwarzschild/PT bridge scale: the local MPLA/PT bridge fixes
  `R_Sigma/R_s = 1`, but `R_s = 2GM/c^2` still requires an active mass/charge.
  The Eddington/PT `R=R_s` throat is null, so it cannot be fed into the current
  regular `h_ab,K_ab` Sigma pipeline without switching to a null-boundary
  formalism.
- Null Sigma scale route: the null-boundary density `sqrt(q) kappa_l` and its
  radial variation are reduced, but still depend on the free Schwarzschild scale
  `R_s`. The canonical PT joint term is reduced and zero. Without the
  generator-rescaling quotient and Barrabes-Israel stress balance, the null
  route does not select an absolute scale.
- Null Barrabes-Israel update: if the missing minus-side transverse curvature
  is proved to be the PT anti-equivariant image of the plus side, the shell
  stress slots are computable conditionally. This is not promoted to active
  closure until the minus-side metric pullback proves the anti-equivariance, and
  it still does not select absolute `R_s`.
- Null/PT bridge update: the Barrabes-Israel stress slots are now computed from
  the active orientation-reversing PT pullback
  `C_minus_ab = -C_plus_ab`; this is not an explicit minus-metric component
  derivation, but it is no longer a free sign assumption. The canonical PT joint
  normalization `l_plus . n_minus = -1` fixes the null-generator rescaling.
  Therefore the remaining null/PT blockers are only structural:
  the radial stationarity equation does not set a finite `R_s`, and no external
  mass/charge/state or action scale is present.
- Null/PT scale map: `build_p0_eft_janus_z2_null_sigma_mass_charge_to_rs_gate.py`
  now gives the strict relation `R_s = 2 G M_bridge / c^2`. It writes a usable
  `null_bridge_rs_scale_inputs.json` only if
  `null_bridge_mass_charge_inputs.json` supplies an active-derived
  `M_bridge_kg` with clean provenance. No such active mass/charge exists in the
  live repo, so the bridge still cannot select an absolute scale.
- Null/PT state-charge mass frontier:
  `build_p0_eft_janus_z2_null_sigma_state_charge_to_mass_bridge_gate.py` now
  provides the strict non-fit reducer
  `M_bridge = N_occ_Z2Sigma * m_bridge_unit_kg`. It accepts only active-derived
  occupation and mass-unit inputs with clean provenance and the explicit policy
  `PT_abs_mass_for_radius`. No live input exists, so this narrows the blocker to
  a real Janus state-selection law for `N_occ_Z2Sigma` and a derived matter/bridge
  mass unit.
- Null/PT global Noether/Souriau mass frontier:
  `build_p0_eft_janus_z2_null_sigma_global_noether_souriau_mass_bridge_gate.py`
  attacks `M_bridge` from the global bimetric/Souriau route. The PT/Souriau
  law fixes the sign pairing `M_minus = -M_plus` and the bridge radius uses the
  absolute mass. It does not fix the absolute magnitude by symmetry alone. A
  live `M_bridge` can only be written from an active bimetric bulk solution mass
  parameter or a global Noether/state charge with clean provenance.
- Null/PT bulk-radius to mass route:
  `build_p0_eft_janus_z2_null_sigma_bulk_rs_to_global_mass_gate.py` handles the
  reverse strict map. If an active Schwarzschild/PT bulk solution supplies an
  absolute `R_s_m` and proves `R_Sigma = R_s`, the gate writes the PT-paired
  global mass solution with `M_plus = c^2 R_s/(2G)` and
  `M_minus = -M_plus`. No such active absolute `R_s_m` exists in the live repo.
- Null/PT LL-brane source extension:
  `build_p0_eft_janus_z2_null_sigma_llbrane_tension_to_rs_gate.py` records the
  only local source route that currently appears mathematically capable of
  selecting the Schwarzschild/PT scale. Following the lightlike-brane
  Einstein-Rosen literature, an explicit LL-brane source at the throat gives
  `m = 1/(16*pi*abs(chi_LL))`, `a0 = 1/8`, and therefore
  `R_s = 1/(8*pi*abs(chi_LL))` in the geometrized inverse-length tension
  convention. This is not a no-extension closure: it requires adopting a real
  LL-brane worldvolume source and deriving `chi_LL`, not fitting it.
- LL-brane bridge chain:
  `run_p0_eft_janus_z2_null_sigma_llbrane_bridge_chain.py` now materializes the
  full extension chain if the active tension input exists:
  `chi_LL_abs_inverse_m -> R_s -> M_plus=-M_minus -> M_bridge -> R_s`.
  In the live workspace the chain blocks at the first stage because
  `null_bridge_llbrane_tension_inputs.json` is absent. The remaining non-fit
  problem is therefore isolated to deriving `chi_LL_abs_inverse_m` from the
  Janus/LL-brane worldvolume dynamics or a legitimate active state condition.
- LL-brane tension frontier:
  `build_p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.py`
  records the final blocker of this extension. The bibliography supplies the
  LL-brane worldvolume framework, horizon straddling, and
  `m = 1/(16*pi*abs(chi_LL))`; it does not supply a Janus-specific value of
  `chi_LL`. A non-fit continuation needs either a Janus-specific LL-brane action,
  an equation of state/boundary state condition, or a quantization/superselection
  law fixing `chi_LL_abs_inverse_m`.
- LL-brane worldvolume tension selection:
  `build_p0_eft_janus_z2_null_sigma_llbrane_worldvolume_tension_selection_gate.py`
  exhausts the local LL-brane equations. The action makes
  `chi_LL = Phi/sqrt(-gamma)` a dynamical composite tension, fixes the horizon
  straddling and the matching constant `a0=1/8`, and relates
  `m = 1/(16*pi*abs(chi_LL))`. It does not select the absolute magnitude of
  `chi_LL`; that requires a Janus PT boundary state, quantization/superselection
  law, or an explicit extension-state input.
- Master action plus LL-brane extension:
  `P0EFTJanusZ2CoverMasterLLBraneActionExtensionGate` and
  `build_p0_eft_janus_z2_cover_master_llbrane_action_extension_gate.py` add
  `S_LLbrane` to the single Janus Z2 cover master action without splitting into
  independent plus/minus actions. The extension supplies a coherent Sigma null
  source and the mass-radius relation, but the combined variation still does not
  select the absolute `chi_LL` magnitude. The next non-fit target is a boundary
  state, quantization, or superselection condition for `chi_LL`.
- LL-brane chi selection audits:
  `build_p0_eft_janus_z2_null_sigma_llbrane_pt_boundary_state_condition_gate.py`
  shows that PT boundary-state invariance fixes the sign/pairing/constancy
  sector but not the magnitude of `chi_LL`. 
  `build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_gate.py` formulates
  a plausible around-Sigma worldvolume flux quantization target, but does not
  yet derive the flux quantum normalization or a non-circular relation from the
  integer flux to `chi_LL_abs_inverse_m`.
- LL-brane flux relation audit:
  `build_p0_eft_janus_z2_null_sigma_llbrane_flux_quantization_relation_audit_gate.py`
  pushes the flux route further. For the 2+1 LL-brane worldvolume, the natural
  gauge flux cycle is the throat `S2`, while `aroundSigma` is only the geometric
  Z2 transport cycle unless a bundle pullback is derived. With
  `integral_S2 F_LL = 2*pi*n/q_LL` and `F_theta_phi=B sin(theta)`, one gets
  `B=n/(2*q_LL)`. This can select a scale only after deriving the charge quantum
  `q_LL`, the auxiliary-metric/physical-area gauge, and the Janus on-shell
  `F2_0`. Without those, flux quantization is only a superselection target and
  does not yet fix `chi_LL`.
- LL-brane branch archive:
  `build_p0_eft_janus_z2_null_sigma_llbrane_branch_archive_gate.py` freezes this
  route as a viable state-parameter extension, not a no-fit closure. The strict
  no-extension branch remains blocked at `chi_LL_abs_inverse_m_not_derived`.
  Reopen is allowed only if `chi_LL` is derived from a global bimetric state,
  a closed flux quantization law, or an explicitly declared extension-state
  input.
- Explicit `chi_LL` state branch:
  `write_p0_eft_janus_z2_null_sigma_effective_chi_ll_state_input.py` can write
  `null_bridge_llbrane_tension_inputs.json` only from a positive finite
  `chi_LL_abs_inverse_m` with clean non-observational provenance. It has no
  default value and must not be used to claim no-fit prediction.
- Global bimetric mass/state scale search:
  `build_p0_eft_janus_z2_global_bimetric_mass_state_scale_search_gate.py` opens
  the parallel search for an absolute scale in the global bimetric/cosmological
  model. Current routes are targets only: exact time-dependent bimetric solution,
  Noether/Souriau state charge, compact-object mass parameter, early-universe
  state, and topology-only. No route currently supplies an absolute scale.
- Global bimetric source-scale audit:
  `build_p0_eft_janus_z2_global_bimetric_source_scale_audit_gate.py` checks the
  M15/M30 anchors. The coupled field equations and Souriau/PT sign pairing are
  available, but they select signs/couplings rather than an absolute mass. The
  remaining non-rustine inputs are a dimensional stress-energy state, a global
  Noether/Hamiltonian mass charge, a coadjoint-orbit mass invariant with state
  selection, or a compact-object mass parameter from an active bimetric solution.
- Global bimetric state writer and bridge pipeline:
  `write_p0_eft_janus_z2_global_bimetric_mass_state_input.py` can declare a
  clean active global mass state with `M_minus=-M_plus`; it has no default and
  rejects observational/legacy provenance. The pipeline
  `run_p0_eft_janus_z2_global_bimetric_to_null_bridge_pipeline.py` then chains
  global mass -> `M_bridge` -> `R_s`. In the live workspace it remains blocked
  because no global bimetric mass state has been derived or declared.
- Global stress-energy mass reducer:
  `build_p0_eft_janus_z2_global_bimetric_stress_energy_mass_reducer_gate.py`
  is the physical front before a direct mass-state declaration. It accepts only
  an active global stress-energy state, either as `M_plus_kg` or as
  `rho_plus_kg_m3 * V_plus_m3`, proves `M_minus=-M_plus`, and writes the same
  global mass solution manifest. No live `global_bimetric_stress_energy_state`
  exists yet.
- Global matter state from Noether baryon volume:
  `build_p0_eft_janus_z2_global_matter_state_from_noether_baryon_volume_gate.py`
  is the strict derivation route for the global matter state. It reduces
  projected Noether baryon number density plus CODATA baryon mass plus active
  projective spatial volume into `rho_plus_kg_m3`, `V_plus_m3`, and `M_plus_kg`.
  It remains blocked because the live workspace still lacks the projected
  baryon Noether charge and active spatial volume normalization.
- Global state prerequisite derivability audit:
  `build_p0_eft_janus_z2_global_state_prerequisite_derivability_audit_gate.py`
  records whether those two prerequisites can be derived now. Current answer:
  no. The charge path is blocked by active plus/minus spinor bundle and Z2/Sigma
  charge projection data. The volume path is blocked by the active
  `R_Sigma_solution_certificate` / dimensional `R_curv` scale. These are real
  non-rustine blockers, not missing Python reducers.
- LL-brane/global-state matching:
  `build_p0_eft_janus_z2_llbrane_global_state_matching_gate.py` relates the two
  scale carriers by equating `R_s = 1/(8*pi*abs(chi_LL))` and
  `R_s = 2*G*M_bridge/c^2`, hence
  `M_bridge = c^2/(16*pi*G*abs(chi_LL))`. This prevents keeping `chi_LL` and
  `M_bridge` as two independent knobs. It does not select the absolute scale:
  an independent state law is still required.
- LL-brane chi selection exhaustive audit:
  `build_p0_eft_janus_z2_null_sigma_llbrane_chi_selection_exhaustive_gate.py`
  now aggregates the local worldvolume EOM, PT boundary state, S2 flux
  quantization relation, and global mass/chi matching. Current verdict:
  none of the active non-fit routes selects `chi_LL_abs_inverse_m`. The
  remaining clean exits are a derived LL gauge-sector law fixing `q_LL`,
  physical S2 area gauge and `F2_0`, an absolute global bimetric/Noether mass
  state matched to `chi_LL`, or an explicitly declared extension-state input.
- Effective initial-state branch: a controlled writer now exists for declaring
  `N_occ_Z2Sigma` without promoting the no-fit branch:
  `write_p0_eft_janus_z2_sigma_effective_initial_state_input.py --n-occ <value>
  --provenance <explicit_non_fit_state_source>`. This writes
  `projected_occupation_state_inputs.json`, which can feed the existing
  effective closure and projected charge writers. No default value is supplied.
- Effective initial-state pipeline: `build_p0_eft_janus_z2_sigma_effective_initial_state_pipeline_gate.py`
  now chains effective closure, projected charge, dimensionless Noether density,
  and Hubble-volume density. In the live workspace it blocks at
  `projected_occupation_state_inputs.json` because no effective state value has
  been declared.
- Effective dimensional-anchor branch: `write_p0_eft_janus_z2_sigma_effective_dimensional_anchor_input.py`
  can write explicit-state `H0_Z2Sigma` and/or `R_curv_Z2Sigma` normalization
  manifests with non-fit provenance. It supplies no default value and rejects
  Planck/LCDM/Z4/fit/demo provenance.
- Effective dimensional-anchor pipeline:
  `build_p0_eft_janus_z2_sigma_effective_dimensional_anchor_pipeline_gate.py`
  now chains declared `H0/R_curv` anchors through the strict background writers
  and into scale-free `omega_k`. Stale reuse is guarded: downstream scale/omega
  steps do not run unless the upstream H0-radius normalization was freshly
  accepted.
- Current refinement: projective stereographic geometry fixes the relative
  throat/collar ratio `R_Sigma_over_ell_collar_Z2Sigma = 1`. This is now written
  to `outputs/active_z2_sigma/effective_partial_closure_from_projective_ratio.json`.
  It does not fix the absolute collar scale.
- Current charge refinement: Z2 projection fixes the weights and reduces the
  deck-invariant charge to `N_Z2Sigma = N_occ`. Noether conservation does not
  select `N_occ`; multiple positive occupations satisfy the same constraints.
  Therefore BAO/plasma normalization remains blocked unless a state-selection
  theorem is derived or `N_occ` is declared as effective initial data.
- Practical effective path now exists:
  `write_p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation.py`
  combines the derived ratio with
  `outputs/active_z2_sigma/projected_occupation_state_inputs.json`. In the live
  workspace it is intentionally blocked because that occupation-state manifest
  is absent. This is an effective-state input path, not a no-fit proof.
- The same occupation-state input can now feed the plasma charge path through
  `write_p0_eft_janus_z2_sigma_projected_charge_from_occupation_state.py`. It
  converts `N_occ_Z2Sigma` into
  `projected_baryon_noether_charge_source_inputs.json`, then lets the strict
  projected-charge writer produce `projected_baryon_noether_charge_inputs.json`.
  Live status is still blocked because
  `outputs/active_z2_sigma/projected_occupation_state_inputs.json` is absent.
- Once the projected charge exists,
  `write_p0_eft_janus_z2_sigma_dimensionless_noether_density_from_charge.py`
  derives the topology-fixed dimensionless density
  `n_b0_Z2Sigma * R_curv_Z2Sigma^3 = N_b,Z2Sigma/(volume_factor*pi^2)`.
  This removes the projective volume-factor ambiguity but still requires the
  physical curvature scale `R_curv_Z2Sigma_m` before Saha/Thomson plasma inputs
  can become dimensional.
- If `H0_Z2Sigma*R_curv_Z2Sigma/c` is available,
  `write_p0_eft_janus_z2_sigma_hubble_volume_noether_density.py` further derives
  `n_b0_Z2Sigma*(c/H0_Z2Sigma)^3`. This is still dimensionless and cannot replace
  the SI baryon density needed by Saha/Thomson recombination, but it isolates the
  remaining dimensional blocker to `H0_Z2Sigma` or `R_curv_Z2Sigma_m`.
- A short density-chain runner now exists:
  `run_p0_eft_janus_z2_sigma_effective_state_density_chain.py`. It runs only the
  occupation-to-charge and dimensionless-density reductions, not BAO. Live status
  is blocked at `projected_occupation_state_inputs.json`, with
  `background_dimensionless_curvature_scale_inputs.json` already present.
- `write_p0_eft_janus_z2_sigma_baryon_density_si_from_dimensionless_invariants.py`
  now converts the dimensionless Noether densities into the standard Saha input
  `early_plasma_baryon_number_density_noether_volume_inputs.json` as soon as
  either `R_curv_Z2Sigma_m` or `H0_Z2Sigma` is active. The conversion is tested
  through the Saha history builder; live status is blocked because the SI scale
  is still absent.
- `run_p0_eft_janus_z2_sigma_plasma_unblock_chain.py` is the short active-plasma
  runner. Current live status: FIRAS temperature and CODATA constants are valid;
  baryon density is blocked by missing projected occupation/charge and missing
  dimensional scale. The runner now continues through Saha inputs,
  `early_plasma.json`, and the Thomson drag readiness check, so the next physical
  blockers are explicit without running the long BAO materialization chain:
  `projected_occupation_state_inputs.json`, then `H0_Z2Sigma` or
  `R_curv_Z2Sigma_m`.
- `run_p0_eft_janus_z2_sigma_scale_free_bao_unblock_chain.py` is the short BAO
  runner. It combines the plasma chain, active primitive obligations, and the
  existing component-to-primitive chi2 path. Current live status:
  `background_scale_free_omega_k_inputs.json` is valid, while
  `early_plasma_inputs.json` and `flrw_component_inputs.json` are missing; BAO
  chi2 remains forbidden.
- Counterterm/dynamic-shell plumbing now calls the minimal-basis coefficient
  solver before consuming `counterterm_minimal_basis_coefficients.json`. The
  live first blocker is therefore the physical trace input
  `counterterm_trace_residual_inputs.json`, i.e. active `R_h_trace` and
  `R_K_trace`, not a missing solver step.
- The counterterm runner now records the actual trace/coefficient cycle:
  minimal coefficients need trace residuals; trace residuals need
  `alpha_res_radial_components`; alpha projection needs active surface
  coefficients. The escape is not another runner: derive active
  `R_h_trace/R_K_trace` from the full Sigma variation, or derive `a0..a3`
  directly from the active Z2/Sigma surface action.
- Lean now mirrors this blocker in
  `P0EFTJanusZ2SigmaCountertermTraceCoefficientCycleGate`: coefficient closure
  requires either active trace residual inputs or a direct active Sigma action
  derivation, and `E_counterterm = 0` is not allowed as a closure shortcut.
- A non-active template/schema for that occupation-state input is generated by
  `build_p0_eft_janus_z2_sigma_projected_occupation_state_schema.py`; it writes
  only `outputs/schemas/projected_occupation_state_inputs.schema.json` and
  `outputs/templates/projected_occupation_state_inputs.template.md`. It also
  writes `outputs/examples/projected_occupation_state_inputs.example.json`, which
  is intentionally outside `outputs/active_z2_sigma` and does not unblock the
  live effective closure path.
- A diagnostic dry-run exists:
  `run_p0_eft_janus_z2_sigma_effective_closure_example_dry_run.py` combines the
  derived projective ratio with the non-active example occupation and writes only
  `outputs/diagnostics/effective_closure_from_example_occupation.diagnostic.json`.
  It confirms the plumbing works while leaving
  `outputs/active_z2_sigma/effective_closure_inputs.json` absent.
- Downstream diagnostic frontier:
  `run_p0_eft_janus_z2_sigma_effective_bao_diagnostic_frontier.py` consumes that
  diagnostic closure. A constant diagnostic primitive writer now exists for
  plumbing only:
  `write_p0_eft_janus_z2_sigma_effective_bao_constant_primitive_diagnostic.py`.
  It can drive the frontier through a DESI DR2 BAO chi2 calculation, but the
  result is marked `diagnostic_only_not_physical_primitives`; it writes no
  active manifest and does not unlock no-fit status. The active primitives still
  need `E_Z2Sigma(z)`, `c_s_over_c_Z2Sigma(z)`,
  `Gamma_drag_over_H0_Z2Sigma(z)`, and `omega_k_Z2Sigma` with
  non-Planck/non-LCDM/non-Z4/non-fit provenance.
- Additional no-extension routes were audited:
  collar reduction of EH/GHY finds the operator `sqrt|h| R[h]`, but its
  coefficient is proportional to an unfixed finite collar thickness; smooth
  Z2 throat regularity fixes parity/junction constraints but not an absolute
  radius; APS/Pin fixes anomaly/parity/integrality classes but not occupied
  fermion number. These routes do not unlock BAO without a new theorem or an
  explicit effective closure.
- New active route opened: `JanusZ2CoverMasterAction`. The target is a single
  cover action on `M_hat` with a Z2 involution, whose projections produce the
  plus/minus sectors and the Sigma junction equations. This is not the archived
  Z4 branch and does not assume Z4 monodromy.
- Initial master-action gates are in place:
  `P0EFTJanusZ2CoverMasterActionGate` and
  `P0EFTJanusZ2CoverMasterLagrangianSkeletonGate`. They enforce one master
  action, no independent plus/minus actions, no `rho_eff` shortcut, no negative
  thermodynamic density postulate, no Z4 reuse and no observational fit. The
  route remains open until the explicit cover Lagrangian, projected variations,
  Sigma junction variation, sign channel and paired Bianchi identity are
  derived.
- Concrete master-action projection code now exists:
  `src/janus_lab/z2_cover_master_action.py` derives
  `G_plus = kappa_J*(T_plus - B_minus_to_plus*T_minus_to_plus)+J_Sigma_plus`
  and
  `G_minus = kappa_J*(T_minus - B_plus_to_minus*T_plus_to_minus)+J_Sigma_minus`
  from the single-cover projection signs. The active manifest lives at
  `outputs/active_z2_cover/projected_equations.json`.
- The paired Bianchi balance is explicit in `src/janus_lab/z2_cover_bianchi.py`:
  Sigma sources must balance the projected divergence of the self and transported
  cross-sector stress tensors. This is not closed until cross-measure transport
  and Sigma variation are derived.
- Measure transport has a concrete calculator:
  `src/janus_lab/z2_cover_measure_transport.py` computes
  `B_minus_to_plus = |J_tau(-,+)| sqrt|g_minus|/sqrt|g_plus|` and the reverse
  factor from active cover determinant inputs. The live runner remains blocked
  until `outputs/active_z2_cover/measure_transport_inputs.json` is supplied.
- A local Sigma-restricted writer now feeds that calculator from the existing
  active sector metrics:
  `write_p0_eft_janus_z2_cover_measure_transport_from_sigma_metrics.py`.
  Current local result on `a_grid=[0.25,0.5,1.0]` is
  `B_minus_to_plus = B_plus_to_minus = 1`. This advances the projected-equation
  bookkeeping, but it is only a local Sigma restriction; the global cover
  determinant transport and Sigma variation are still open.
- Sigma source extraction is now concrete:
  `src/janus_lab/z2_cover_sigma_source.py` maps boundary metric-variation
  coefficients to projected surface sources through
  `T_Sigma^ab = -2 alpha_h^ab` and
  `J_Sigma^ab = orientation*T_Sigma^ab`. The live source runner remains blocked
  until `outputs/active_z2_cover/sigma_alpha_h_inputs.json` exists.
- A strict bridge from surface h/K density to cover Sigma source inputs exists:
  `write_p0_eft_janus_z2_cover_sigma_alpha_h_from_surface_hk.py` consumes
  `outputs/active_z2_sigma/surface_hk_active_density_coefficients.json` and
  `outputs/active_z2_sigma/surface_hk_isotropic_geometry.json`. It is currently
  blocked because neither active manifest exists. This is the next physical
  input needed for deriving `J_Sigma` rather than naming it symbolically.
- Bianchi can now attach a derived Sigma source via
  `derive_p0_eft_janus_z2_cover_bianchi_with_sigma_source.py`. It remains
  blocked until `sigma_source.json` is produced; after that the remaining
  closure is the divergence of `J_Sigma` plus cross-measure transport.
- Active `R_Sigma` counterterm chain is now executable:
  `run_p0_eft_janus_z2_sigma_counterterm_chain.py` writes the already-derived
  geometry and torsionless Immirzi pieces, then attempts the concrete h/K route:
  Riccati normal-flow primitives -> radial geometry -> alpha radial projection.
  The live blocker is now
  `outputs/active_z2_sigma/surface_hk_normal_flow_geometry_inputs.json`, which
  must provide active `h_ab`, `K_ab`, and `R_nabn` on Sigma. Downstream this emits
  `counterterm_alpha_res_radial_components.json`, then `R_h_trace/R_K_trace`,
  `counterterm_lct_radial_profile.json`, and `rsigma_E_counterterm.json`. Do not
  set `E_counterterm = 0` while this is open.
- The round-throat counterterm now has an analytic closure:
  `E_counterterm(R) = sqrt(det q) * (3 a0 R^2 + 6 epsilon_Z2 a1 R + 9 a2 + 3 a3)`.
  This removes the need to sample `E_counterterm` before a radius is known. The
  helper `positive_round_throat_radius_roots` solves the positive algebraic roots
  once `a0..a3` are active. The remaining non-fit blockers are therefore the
  active surface h/K density coefficients `a0..a3` and either the coupled radius
  equation using that quadratic closure or an independent global regularity
  equation.
- Minimal h/K coefficient diagnostics are explicit: the basis
  `L_Sigma = a0 + a1 K + a2 K^2 + a3 K_ab K^ab` is not enough by itself to fix
  the coefficients. The active route must derive either
  `counterterm_alpha_res_radial_components.json` from the full Sigma variation
  or `surface_hk_active_density_coefficients.json` directly from the active
  surface action. Reusing the linear `K` term as a new counterterm is forbidden
  because it duplicates the Cartan/GHY partition.
- Effective-closure branch has a strict input gate:
  `outputs/active_z2_sigma/effective_closure_inputs.json` may provide only
  `R_Sigma_over_ell_collar_Z2Sigma` and
  `projected_baryon_number_charge_Z2Sigma`, with
  `source = effective_initial_data`, no Planck/LCDM/Z4/fit provenance, and
  `full_no_fit_prediction_ready = false`. The gate is intentionally red until
  those effective initial data are explicitly supplied.
- Effective BAO path gate is now explicit. Even after the two-parameter
  effective closure is supplied, BAO is not ready from those two numbers alone:
  it still needs `E_Z2Sigma(z)`, `omega_k_Z2Sigma`, `c_s/c`, and
  `Gamma_drag/H0` from non-Planck, non-LCDM, non-Z4 provenance.
- Effective scale-free BAO chi2 runner exists separately from the strict
  `active_derived` path:
  `outputs/active_z2_sigma/effective_bao_scale_free_primitive_inputs.json`
  can feed `build_p0_eft_janus_z2_sigma_effective_bao_scale_free_chi2_gate.py`.
  It solves `Gamma_drag/H0 = E`, integrates `H0*r_d/c`, and evaluates DESI DR2
  BAO chi2 while keeping `full_no_fit_prediction_ready = false`.
- One-command effective BAO end-to-end gate exists:
  `build_p0_eft_janus_z2_sigma_effective_bao_end_to_end_gate.py`.
  It requires both `effective_closure_inputs.json` and
  `effective_bao_scale_free_primitive_inputs.json`, verifies the primitive
  manifest hashes the closure manifest, then reports `z_d`, `H0*r_d/c`, DESI
  prediction/residual vectors and effective chi2. In the live workspace it is
  intentionally blocked until those manifests are supplied.
- Parameter-entry effective BAO gate exists:
  `build_p0_eft_janus_z2_sigma_effective_bao_from_parameter_inputs_gate.py`.
  It consumes `outputs/active_z2_sigma/effective_bao_parameter_inputs.json`,
  writes the two effective manifests canonically, hashes the closure manifest,
  and runs the end-to-end effective BAO gate. It remains blocked until explicit
  effective parameters and primitive arrays are supplied.
- `effective_bao_parameter_inputs.json` now has a reusable validator in
  `src/janus_lab/z2_sigma_effective_parameter_inputs.py`; it enforces aligned
  positive primitive arrays, explicit two-parameter effective initial data, no
  Planck/LCDM/Z4/fit flags, and `full_no_fit_prediction_ready = false`.
- A schema/template gate now emits
  `outputs/schemas/effective_bao_parameter_inputs.schema.json` and
  `outputs/templates/effective_bao_parameter_inputs.template.md`. The template
  is intentionally non-executable: it does not write an active manifest and
  keeps `full_no_fit_prediction_ready = false`. The schema now requires the
  dimensionless throat/collar ratio `R_Sigma_over_ell_collar_Z2Sigma` and
  rejects the deprecated dimensionful `R_Sigma_effective_Mpc` closure.
- Non-effective geometric route reopened:
  `derive_p0_eft_janus_z2_sigma_global_regular_tunnel_radius_selection_gate.py`
  formulates the active target
  `F_reg(R_Sigma/ell_collar)=0` from global defect-free Z2 tunnel regularity.
  This route uses no torus replacement, no Planck/LCDM/Z4 input and no fit. It
  does not yet fix the ratio: the blocker is computing `F_reg` from the active
  collar embedding, normal-frame holonomy, endpoint gluing mismatch and
  distributional Bianchi/junction residual.
- `F_reg` is now decomposed by
  `derive_p0_eft_janus_z2_sigma_global_regular_functional_components_gate.py`
  into three geometric channels:
  normal-frame holonomy defect, collar endpoint mismatch, and
  junction/Bianchi defect. The route remains blocked until active plus/minus
  collar metrics, normal connection, Z2 deck pullback and Sigma stress/normal
  flux data are derived.
- A strict `F_reg(lambda)` solver now exists:
  `build_p0_eft_janus_z2_sigma_global_regular_freg_solver_gate.py` consumes
  `outputs/active_z2_sigma/global_regular_freg_components.json`, rejects
  Planck/LCDM/Z4/fit/torus-replacement provenance, computes
  `F_reg(lambda)` from the three defect channels, and selects
  `R_Sigma/ell_collar` only if a unique regular root is present. It remains red
  until the active component arrays are derived.
- The expected component manifest is now indexed by
  `build_p0_eft_janus_z2_sigma_global_regular_freg_components_schema_gate.py`,
  which emits `outputs/schemas/global_regular_freg_components.schema.json` and
  `outputs/templates/global_regular_freg_components.template.md` without writing
  an active manifest.
- The concrete primitive frontier for the `F_reg` components is listed by
  `derive_p0_eft_janus_z2_sigma_global_regular_freg_data_frontier_gate.py`:
  normal connection on the collar, endpoint collar metrics plus Z2 pullback,
  and Sigma stress divergence plus bulk normal-flux jump.
- A primitive materialization path now exists:
  `build_p0_eft_janus_z2_sigma_global_regular_freg_from_primitives_gate.py`
  consumes `outputs/active_z2_sigma/global_regular_freg_primitives.json`,
  computes the three `F_reg` components, writes
  `global_regular_freg_components.json`, and runs the unique-root solver. It
  remains blocked until actual active collar/endpoint/Bianchi primitives exist.
- The primitive manifest itself is indexed by
  `build_p0_eft_janus_z2_sigma_global_regular_freg_primitives_schema_gate.py`,
  which emits `outputs/schemas/global_regular_freg_primitives.schema.json` and
  `outputs/templates/global_regular_freg_primitives.template.md`.
- A local transparent collar probe now exists:
  `build_p0_eft_janus_z2_sigma_global_regular_local_transparent_probe.py`.
  It uses a zero normal connection, matched endpoint metrics and zero normal
  flux. Result: every sampled `R_Sigma/ell_collar` has zero defect, so local
  transparent regularity is scale-flat and cannot select the ratio. The next
  required signal must be genuinely global/nonlocal.
- A diagnostic projective twist probe now exists:
  `build_p0_eft_janus_z2_sigma_global_twist_holonomy_probe.py`. It shows that a
  nonlocal normal-frame holonomy twist can select a unique
  `R_Sigma/ell_collar` inside the `F_reg` machinery. It is not an active proof:
  the missing step is deriving that twist from the projective Z2 collar
  geometry/action.
- The proof obligation for promoting that probe is explicit in
  `derive_p0_eft_janus_z2_sigma_projective_holonomy_twist_derivation_target_gate.py`:
  derive the deck action on the normal frame bundle, derive
  `omega_perp(lambda,u)` from the active collar metric, include the deck-frame
  map in the closed collar loop, then prove non-flat unique-root behavior.
- The first projective-holonomy sub-obligation is now isolated:
  `derive_p0_eft_janus_z2_sigma_deck_normal_frame_action_gate.py` derives the
  Z2 collar-normal reversal as `deck_frame_map = -1` on the normal line. This
  does not fix the radius; it only supplies the projective frame map needed by
  the deck-corrected holonomy.
- The next normal-connection sub-obligation now has an executable calculator:
  `src/janus_lab/z2_sigma_normal_connection.py` computes
  `omega_perp_AB=<N_A,D_u N_B>` from active normal frames, frame derivatives,
  the collar connection matrix and the ambient metric. The live gate
  `build_p0_eft_janus_z2_sigma_normal_connection_from_frame_gate.py` remains
  red until `outputs/active_z2_sigma/normal_connection_frame_primitives.json`
  is supplied.
- The expected normal-frame primitive manifest is indexed by
  `build_p0_eft_janus_z2_sigma_normal_connection_frame_primitives_schema_gate.py`.
  It emits `outputs/schemas/normal_connection_frame_primitives.schema.json` and
  `outputs/templates/normal_connection_frame_primitives.template.md` without
  writing active data.
- Active next track: derive observational equations from the closed
  `Z2_tunnel_Sigma` base, not from archived cyclic Z4 modules.
- BAO active readiness now reads the strict active manifest path
  `outputs/active_z2_sigma/bao_inputs.json`; the path is currently missing, so
  `H_Z2Sigma`, `c_s_Z2Sigma`, `z_d_Z2Sigma`, `r_d_Z2Sigma` and DESI chi2 remain
  blocked rather than mocked.
- BAO component writing now requires three strict upstream manifests:
  `outputs/active_z2_sigma/background_scalars.json`,
  `outputs/active_z2_sigma/flrw_components.json`, and
  `outputs/active_z2_sigma/early_plasma.json`. All three are currently missing,
  so `outputs/active_z2_sigma/bao_component_inputs.json` is not written.
- `outputs/active_z2_sigma/background_scalar_inputs.json` is now the strict
  upstream input manifest for writing `background_scalars.json`; it must provide
  active `H0_Z2Sigma`, `omega_k_Z2Sigma`, and `G_Z2Sigma` provenance with no
  observational H0 fit, Planck/LCDM prior, or archived Z4 reuse.
- A strict background-scalar assembler can now write
  `background_scalar_inputs.json` from active `background_H0_inputs.json`,
  `background_curvature_inputs.json`, and `background_gravity_inputs.json`;
  it remains blocked until those three active scalar inputs exist.
- Strict atomic background writers can now produce those three scalar inputs
  from active `background_H0_normalization_inputs.json`,
  `background_curvature_normalization_inputs.json`, and
  `background_gravity_normalization_inputs.json`; they remain blocked until the
  active scale, projective curvature and low-energy gravity convention are
  derived upstream.
- `outputs/active_z2_sigma/flrw_component_inputs.json` is now the strict
  upstream input manifest for writing `flrw_components.json`; it must provide
  active Cartan-GHY, Holst/Nieh-Yan, matter-flux, and counterterm FLRW arrays
  with non-Planck, non-LCDM, non-Z4 provenance.
- Matter-flux has a strict zero-component subpath:
  `outputs/active_z2_sigma/matter_flux_transparency_inputs.json ->
  matter_flux_zero_components.json`. It only writes zeros when active Sigma
  transparency is derived; it does not by itself unlock the full FLRW manifest.
- The matter-flux frontier now marks transparency as the nearest non-circular
  route: active projection requires `X_+/-[R_Sigma]`, while transparency can
  reduce `E_matterFlux` without fitting `R_Sigma(a)`.
- The transparency input itself can be written only from the active
  no-normal-current gate plus active bulk-stress normal-flux cancellation/zero
  projection and an active `a_grid`.
- The transparency gate itself now also requires active normal-current
  readiness, projected Dirac normal current readiness and bulk normal-flux
  projection readiness before accepting any derived zero/cancellation boolean.
- A strict merge gate can combine
  `flrw_component_inputs_without_matter_flux.json + matter_flux_zero_components.json`
  into `flrw_component_inputs.json`, but only with active provenance and aligned
  grids.
- Effective-fluid and numerical-background gates now consume those strict
  manifests when present. Valid temporary manifests prove that `rho_eff/p_eff`
  and `H_Z2Sigma(a)` readiness can turn true without Planck/LCDM/Z4 reuse.
- Early-plasma density and Thomson-drag gates now consume the strict
  `outputs/active_z2_sigma/early_plasma.json` artifact when present. The true
  open derivations are active baryon/photon normalization, ionization history,
  free-electron density, and `Gamma_drag_Z2Sigma`.
- `outputs/active_z2_sigma/early_plasma_inputs.json` is now the strict upstream
  input manifest for writing `early_plasma.json`; it must provide active
  baryon/photon/ionization/Thomson normalizations with non-Planck, non-LCDM,
  non-Z4 provenance.
- A strict early-plasma assembler can now write `early_plasma_inputs.json` from
  active `early_plasma_baryon_photon_inputs.json` and
  `early_plasma_ionization_thomson_inputs.json`; it remains blocked until those
  two active manifests exist.
- Strict upstream writers can now produce those two partial manifests from
  active `early_plasma_baryon_photon_normalization_inputs.json` and
  `early_plasma_ionization_thomson_normalization_inputs.json`; both remain red
  until real active normalizations are supplied.
- The temporary BAO dry-run now exercises the full strict-manifest plumbing:
  `background_scalars.json + flrw_components.json + early_plasma.json ->
  bao_component_inputs.json -> bao_inputs.json -> DESI chi2`. It remains
  `dry_run_only`, not an official BAO evaluation.
- `build_p0_eft_janus_z2_sigma_active_inputs_to_official_bao_gate.py` now
  provides the official one-command path from the three active input manifests
  to DESI DR2 BAO chi2. It remains blocked until real active input manifests
  exist.
- The official one-command BAO gate uses an atomic preflight: it does not write
  any intermediate official manifest unless all three active input manifests are
  present.
- The BAO readiness audit now exposes a `remaining_artifact_frontier` and a
  `physical_derivation_frontier`. Current plumbing gaps should not be expanded
  into more writer gates until the listed active physical inputs exist.
- The BAO readiness audit now also reports
  `nearest_component_frontier = cartan_ghy`: builders are ready, but live
  evaluation still needs active `DeltaK_s/tau(a)` from the tunnel embedding and
  `background_scalars.json` for `kappa*rho_crit0`.
- Current physical frontier:
  active `H0/G/omega_k` conventions, active `R_Sigma(a)` and `X_+/- (a)`,
  Holst/Nieh-Yan FLRW stress, Sigma counterterm stress, Sigma transparency,
  baryon/photon normalization, and ionization/Thomson drag inputs.
- Normalization policy: `H0_Z2Sigma` is not an observational H0 fit in BAO
  ratios when `H_Z2Sigma`, `z_d` and `r_d` are recomputed self-consistently.
  It still enters the physical drag equation `Gamma_drag = H`, so it cannot be
  varied independently of the active early-plasma inputs.
- A scale-free BAO formulation is available:
  `E_Z2Sigma(z)`, `c_s^Z2Sigma/c`, `z_d^Z2Sigma`,
  `H0*r_d/c = integral (c_s/c)/E dz`. It is equivalent to the dimensional
  DESI ratio calculator and does not unblock the official BAO gate by itself.
  The active builders now expose `E_Z2Sigma(z)` from normalized effective
  density and `Gamma_drag^Z2Sigma/H0` for scale-free drag solving.
- The active early-plasma helpers now expose `c_s^Z2Sigma/c` directly from
  active baryon/photon densities. The builder is ready; values remain blocked
  until `rho_baryon_Z2Sigma` and `rho_photon_Z2Sigma` are derived.
- Minimal scale-free BAO primitive contract:
  `E_Z2Sigma(z)`, `c_s^Z2Sigma/c`, `Gamma_drag^Z2Sigma/H0`, and
  `omega_k_Z2Sigma`. From those, the active path derives `z_d`, `rhat_d`,
  DESI DR2 BAO prediction vector and chi2. This contract is not ready until
  the primitives are derived from active Z2/Sigma physics. The contract gate now
  validates the strict `bao_component_inputs.json` manifest dynamically: if that
  active manifest exists and passes provenance checks, the scale-free primitive
  contract becomes ready without any Planck/LCDM or archived Z4 input. The
  generated `bao_scale_free_inputs.json` stores `E_Z2Sigma`, `c_s/c`,
  `Gamma_drag/H0`, `z_d`, and `rhat_d` explicitly for audit. The scale-free
  chi2 gate now reports primitive samples, prediction/residual vector lengths,
  and `Gamma_drag/H0` availability alongside the DESI chi2.
- A one-command scale-free BAO chi2 gate now runs the strict chain
  `background_scalar_inputs + flrw_component_inputs + early_plasma_inputs ->
  bao_component_inputs -> bao_scale_free_inputs -> DESI chi2`. It remains
  blocked in the live workspace until the active physical input manifests exist.
- The BAO readiness audit now reports a separate canonical scale-free artifact:
  `outputs/active_z2_sigma/bao_scale_free_inputs.json`, driven by
  `E_Z2Sigma`, `c_s/c`, `Gamma_drag/H0`, and `omega_k_Z2Sigma`, with no
  observational H0 fit or archived Z4 input.
- A primitive-entry BAO gate now accepts
  `outputs/active_z2_sigma/bao_scale_free_primitive_inputs.json` with active
  `E_Z2Sigma`, `c_s/c`, `Gamma_drag/H0`, and `omega_k_Z2Sigma`, solves
  `Gamma_drag/H0 = E` for `z_d`, writes `bao_scale_free_inputs.json`, then runs
  the DESI DR2 scale-free chi2. The primitive manifest now has a public strict
  writer/loader in `z2_sigma_active_inputs.py`, so future physical derivations do
  not hand-write JSON. The live gate remains red until that primitive manifest is
  derived from Z2/Sigma physics.
- A split primitive assembler is available:
  `bao_scale_free_background_primitive_inputs.json` supplies `E_Z2Sigma` and
  `omega_k_Z2Sigma`; `bao_scale_free_plasma_primitive_inputs.json` supplies
  `c_s/c` and `Gamma_drag/H0`. The assembler writes the canonical
  `bao_scale_free_primitive_inputs.json`. Both split manifests now have public
  strict writers/loaders in `z2_sigma_active_inputs.py`.
- A split-primitive-to-chi2 gate now composes the direct canonical path:
  background primitive + plasma primitive -> primitive manifest -> scale-free
  BAO inputs -> DESI DR2 prediction/residual vectors and chi2.
- A primitive derivation frontier gate now records the exact upstream physics
  still required before DESI BAO can be evaluated from active Z2/Sigma:
  derive `E_Z2Sigma`, `omega_k_Z2Sigma`, `c_s/c`, and `Gamma_drag/H0` into the
  two split primitive manifests. It remains red until both manifests are valid
  and aligned.
- A physical-input obligation gate now records the three strict active manifests
  that must exist before that primitive frontier can feed DESI DR2:
  `background_scalar_inputs.json`, `flrw_component_inputs.json`, and
  `early_plasma_inputs.json`. It forbids mocks, compressed Planck/LCDM inputs,
  archived Z4 reuse, observational H0 fits, and phenomenological Holst BAO scan
  values.
- An early-plasma physical-input obligation gate now isolates the `c_s` and
  `Gamma_drag` side of the BAO blocker: active baryon/photon normalizations plus
  active ionization/Thomson normalizations are required before the existing
  builders may derive `c_s/c`, `Gamma_drag`, and then `z_d` with `E_Z2Sigma`.
- When a strict active `bao_component_inputs.json` exists, a component-to-split
  primitive gate can now write the two scale-free primitive manifests directly:
  background primitives from the active effective fluid/curvature and plasma
  primitives from the active photon-baryon/drag sector.
- A narrower background-only scale-free gate can now write
  `bao_scale_free_background_primitive_inputs.json` from active
  `flrw_components.json` plus `background_scale_free_omega_k_inputs.json`,
  without passing through a dimensional `H0` BAO component manifest.
- A narrower plasma-only scale-free gate can now write
  `bao_scale_free_plasma_primitive_inputs.json` from active `early_plasma.json`
  plus active `background_H0_inputs.json`, producing `c_s/c` and
  `Gamma_drag/H0` with no observational H0 fit or archived Z4 input.
- A one-command component-to-primitive-chi2 gate now composes the auditable path
  `bao_component_inputs.json -> split primitives -> canonical primitive ->
  scale-free BAO inputs -> DESI DR2 chi2`. It remains red in the live workspace
  until the active component manifest exists.
- A one-command active-inputs-to-primitive-chi2 gate now composes the full
  auditable path from `background_scalar_inputs.json`, `flrw_component_inputs.json`
  and `early_plasma_inputs.json` through the primitive chain to DESI DR2 chi2.
  It uses atomic preflight and writes no intermediates until all three inputs
  exist; it now also blocks if the counterterm radial reduction frontier is not
  closed, preventing placeholder `counterterm_rho/p` arrays from reaching BAO.
- Canonical first BAO artifact to produce:
  `outputs/active_z2_sigma/background_scalars.json`, sourced only from active
  `background_H0_inputs.json`, `background_curvature_inputs.json`, and
  `background_gravity_inputs.json`. This must not use compressed Planck/LCDM,
  archived Z4, or an observational H0 fit.
- Curvature policy: the closed projective/tunnel `2:1` topology does not by
  itself fix FLRW `k_Z2Sigma` or numeric `omega_k_Z2Sigma`; derive the active
  spatial metric branch and FLRW curvature radius/embedding scale before
  writing `background_curvature_inputs.json`. The branch contract is declared
  through `R3_Z2Sigma = 6*k_Z2Sigma/R_curv_Z2Sigma^2`; its values remain blocked
  until `X_+/- (a)` or the induced FLRW spatial metric is derived.
- `P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGate` is now the conditional
  active route for the sign: an active `S3 -> RP3` spatial slice can write
  `k_Z2Sigma = +1`, while `R_curv_Z2Sigma` and `omega_k_Z2Sigma` remain open.
- `P0EFTJanusZ2SigmaRP3SpatialSliceInputWriterFromProjectiveFoliationGate`
  narrows the required proof: supply an active projective foliation whose FLRW
  leaves are antipodal `S3 -> RP3` leaves before the sign writer can pass.
- `P0EFTJanusZ2SigmaProjectiveFoliationCompatibilityGate` blocks the shortcut
  from global `S4 -> RP4` to a single `RP3` FLRW slice: generic `S3` leaves are
  paired by the antipodal map, so an active invariant-leaf time gauge must
  still be derived for the `RP3` branch.
- `P0EFTJanusZ2SigmaProjectiveSpatialSliceTopologyBranchGate` tracks the other
  live possibility: paired leaves select an `S3` representative branch, not an
  `RP3` branch, and the volume factor changes from `1` to `2`. The next active
  input is `outputs/active_z2_sigma/time_gauge_leaf_action_inputs.json`.
- `P0EFTJanusZ2SigmaSignedCoverTimeParityGate` is now the upstream provenance
  writer: `outputs/active_z2_sigma/signed_cover_time_coordinate_inputs.json`
  must supply the active signed `S4` cover time coordinate before parity can be
  written.
- `P0EFTJanusZ2SigmaTimeGaugeLeafActionInputWriterGate` narrows that blocker to
  `outputs/active_z2_sigma/active_time_coordinate_parity_inputs.json`; even
  parity selects invariant `RP3`, odd parity selects paired `S3`.
- `omega_k_Z2Sigma` formula path is now explicit:
  `omega_k = -k_Z2Sigma c^2 / (H0_Z2Sigma^2 R_curv_Z2Sigma^2)`.
  Formula and strict writer are ready; values remain blocked until the active
  FLRW branch/tunnel embedding fixes both `k_Z2Sigma` and `R_curv_Z2Sigma` and
  supplies `background_curvature_branch_inputs.json`.
- `P0EFTJanusZ2SigmaH0RadiusFLRWToScaleFreeBackgroundPipelineGate` now validates
  the strict background route `H0,R_curv,k + flrw_components -> omega_k ->
  E_Z2Sigma(z)` for scale-free BAO. It remains red live until active `H0`,
  `R_curv/k`, and FLRW component densities are supplied.
- `P0EFTJanusZ2SigmaCurvatureScaleFLRWToScaleFreeBackgroundPipelineGate` validates
  the direct scale-free background route
  `k + H0*R_curv/c + flrw_components -> omega_k -> E_Z2Sigma(z)`. The live
  `omega_k_Z2Sigma` side is now evaluable; the remaining background blocker is
  the active `flrw_components.json` manifest, now decomposed into Cartan-GHY,
  Holst/Nieh-Yan, counterterm and transparent matter-flux component frontiers.
- `P0EFTJanusZ2SigmaDimensionlessCurvatureScaleFromBranchGate` now bridges the
  physical curvature branch into the direct scale-free route by deriving
  `H0*R_curv/c` from `background_curvature_branch_inputs.json` when that active
  manifest exists. It does not supply or fit `H0` or `R_curv`.
- `P0EFTJanusZ2SigmaDimensionfulScaleSeparationObligationGate` makes that
  separation explicit: the product `H0*R_curv/c` is not invertible into separate
  dimensional `H0` or `R_curv`, and cannot supply volume or `Gamma_drag/H0`.
- `P0EFTJanusZ2SigmaBackgroundPhysicalInputObligationGate` isolates the
  background side of the BAO blocker: active `H0_Z2Sigma`, active FLRW
  curvature branch (`k_Z2Sigma`, `R_curv_Z2Sigma`), and active `G_Z2Sigma`
  must be supplied before `E_Z2Sigma` and `Gamma_drag/H0` can be evaluated.
- `P0EFTJanusZ2SigmaBackgroundGravityCODATAConventionGate` can now write the
  active `G_Z2Sigma` input from the explicit NIST/CODATA Newtonian gravity
  convention. This is not a Planck/LCDM prior and not a cosmological fit.
- `P0EFTJanusZ2SigmaEarlyPlasmaCODATAConstantsGate` can now write the
  CODATA constants needed by the early-plasma side: radiation constant, proton
  mass as baryon-mass convention, Thomson cross-section, electron mass,
  `k_B`, `hbar`, `eV`, and hydrogen ionization energy. This does not fix
  active `rho_baryon0`, `T_gamma0`, `x_e`, or composition.
- `P0EFTJanusZ2SigmaEarlyPlasmaModelNormalizationAssemblerGate` can combine
  CODATA constants and FIRAS temperature with a future active
  model-normalization manifest to write the existing baryon/photon and
  ionization/Thomson split inputs. It stays red until baryon and ionization
  normalizations are derived.
- The model-normalization manifest now needs only active baryon number density,
  ionization fraction and electrons-per-baryon. `rho_baryon0` is derived from
  `n_b0*m_b` using the CODATA baryon-mass convention.
- `P0EFTJanusZ2SigmaEarlyPlasmaPhotonTemperatureFIRASGate` records the direct
  non-compressed COBE/FIRAS monopole temperature `T_gamma0 = 2.72548 K`. It is
  not a Planck/LCDM compressed parameter and not an observational fit, but it
  also does not fix baryon or ionization normalizations.
- `P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityFIRASCODATAGate` derives
  `rho_photon0 = a_rad*T_gamma0^4` from CODATA plus FIRAS. This closes the
  photon-normalization sub-block while leaving baryon and ionization inputs open.
- `P0EFTJanusZ2SigmaEarlyPlasmaPhotonDensityHistoryFIRASCODATAGate` derives the
  conserved photon history `rho_photon(z)=rho_photon0*(1+z)^4` from that closed
  photon normalization. It does not close baryon loading or drag opacity.
- `P0EFTJanusZ2SigmaEarlyPlasmaSahaIonizationReadinessGate` declares the
  non-Planck Saha-equilibrium route for `x_e(z)` using active `n_b(z)` and
  FIRAS `T_gamma(z)`. It remains red until active baryon number is available;
  Peebles/RECFAST precision remains a later upgrade.
- `P0EFTJanusZ2SigmaSahaIonizationHistoryGate` now computes the active hydrogen
  Saha history once `n_b0`, FIRAS `T_gamma0`, and CODATA/NIST constants exist.
  It remains red in the live pipeline until the Noether/volume baryon-number
  density is derived and the resulting history is fed into the plasma manifest.
- `P0EFTJanusZ2SigmaEarlyPlasmaSahaInputsAssemblerGate` can assemble
  `early_plasma_inputs.json` from CODATA constants, FIRAS `T_gamma0`, and the
  active Saha history. It preserves the grid-valued `x_e(z)` and bypasses the
  old scalar `ionization_fraction_Z2Sigma` path when a history is available.
- `P0EFTJanusZ2SigmaNoetherVolumeToSahaEarlyPlasmaPipelineGate` validates the
  full downstream route `N_b/V0 -> n_b0 -> x_e(z) -> early_plasma_inputs ->
  early_plasma.json`. It remains red live because the active projected baryon
  Noether charge and active spatial volume are not yet derived. Explicit active
  charge/volume manifests passed by path now build `n_b0` and downstream
  Saha/plasma fixtures without coupling to default output paths. The live report
  now exposes `baryon_density`, `saha_history`, `saha_inputs`, and
  `early_plasma_manifest` as separate frontiers.
- `P0EFTJanusZ2SigmaCurvatureChargeToSahaEarlyPlasmaPipelineGate` extends that
  route upstream to `R_curv,k -> RP3 volume -> N_b/V0 -> x_e(z) -> plasma`.
  It reduces the live plasma blocker to active curvature radius/branch plus
  projected baryon Noether charge. Its report now exposes three nested
  frontiers: Dirac charge-boundary projection, spatial-volume input from the
  curvature branch, and downstream baryon-density/Saha manifest assembly.
- `P0EFTJanusZ2SigmaSpatialVolumeInputWriterFromCurvatureBranchGate` now
  preflights the live curvature-branch assembler; a dimensionful curvature
  branch fixture cannot self-certify the active spatial volume.
- `P0EFTJanusZ2SigmaPhysicalInputsToScaleFreeBAOChi2Gate` now composes the
  physical active route end-to-end:
  `k + H0*R_curv/c + flrw_components -> background primitive`,
  `R_curv/k + projected baryon charge + CODATA/FIRAS/Saha -> plasma primitive`,
  then `split primitives -> scale-free DESI DR2 prediction/residual vectors and
  chi2`. It uses the direct FIRAS photon-temperature manifest by default and
  now reports structured frontiers for background, curvature+charge plasma, and
  plasma primitive readiness, including the nested `early_plasma_manifest` and
  `active_h0_manifest` plasma blockers. The H0 blocker is wired to the active
  `background_H0_normalization_inputs.json -> background_H0_inputs.json` writer.
  It also emits `physical_frontier_summary`, a flat checklist of the remaining
  background, matter-flux, curvature-volume, baryon-charge and early-plasma
  blockers.
  It remains red live until active `H0`, `R_curv/k`, FLRW components, projected
  baryon Noether charge, and active early-plasma/H0 manifests are supplied.
- `P0EFTJanusZ2SigmaBAOActivePrimitivePhysicalInputObligationGate` now consumes
  the active scale-free `omega_k_Z2Sigma` artifact when present; live BAO
  primitive readiness is therefore blocked by FLRW component inputs and
  early-plasma inputs, not by raw Planck/LCDM background scalars.
- `P0EFTJanusZ2SigmaFLRWComponentsFromComponentSourcesPipelineGate` now composes
  the active source-component route to `flrw_components.json`:
  Cartan-GHY, Holst/Nieh-Yan, counterterm and transparent matter-flux component
  manifests are merged and written through the strict FLRW manifest writer. It
  remains red live until those component manifests are derived. The non-matter
  assembler now reports diagnostic subfrontiers for Cartan-GHY, Holst/Nieh-Yan,
  and counterterm components, so this blocker is traceable without invoking
  archived Z4 or Planck/LCDM inputs.
- The throat-radius frontier now reports the nearest radial blockers explicitly:
  Cartan-GHY is structurally reduced, but `R_Sigma(a)` and then `DeltaK_s/tau(a)`
  remain blocked until matter-flux and counterterm radial blocks are reduced.
- The active embedding-to-FLRW-K adapter now reports the exact upstream frontier:
  derive `R_Sigma(a)`, `X_+/- (a)`, tangent frames, unit normals, and
  `DeltaK_s/tau(a)` before Cartan-GHY can write live FLRW components. This is
  the current non-circular Cartan path; it does not use archived Z4 or
  Planck/LCDM inputs.
- The `R_Sigma` solution bridge now writes both
  `active_tunnel_embedding_geometry_inputs.json` and
  `background_curvature_branch_inputs.json` when, and only when, a strict
  active no-fit `rsigma_solution_certificate.json` exists and the throat-radius
  frontier is closed.
- The same bridge now writes the two atomic dimensional normalization inputs
  `background_H0_normalization_inputs.json` and
  `background_curvature_radius_normalization_inputs.json` from that strict
  certificate, keeping `H0_Z2Sigma` and `R_curv_Z2Sigma` separate rather than
  inverting the scale-free product.
- The matter-flux transparency input writer now requires both the normal-current
  closure and the bulk-stress projection/cancellation readiness before writing
  a zero-flux transparency manifest; closure booleans alone are not sufficient.
- The bulk-stress normal-flux route now imports the active bulk stress `of(a)`
  frontier explicitly; projected zero-flux cannot close while `T_+/-^{mu nu}(a)`
  are still unavailable.
- The counterterm tetrad residual channel now declares the metric subchannel
  formula `R_e_metric^{aI}` from `delta h_ab(delta e)`, but the active value is
  still not ready; this does not close the full tetrad residual channel.
- A strict counterterm tetrad metric-residual coefficient writer now exists. It
  computes `R_e_metric^{aI}` only from active `R_h_ab` and `e_bI_on_Sigma`
  inputs and remains red until those artifacts exist.
- The spinor boundary projection map now imports the projective-gluing normal
  orientation sign `epsilon_Z2=-1`; Z2 normal orientation is partial-ready, but
  boundary spinors, unit-normal Clifford action, idempotence and self-adjointness
  still block the projected spinor route.
- The coupled radius-flux function-space gate now imports the standard Sobolev
  trace/product threshold transport into the active blocker report: trace and
  product thresholds are closed, while normal/tangent frame trace continuity
  remains blocked on the active embedding.

## Pure math closure

- [x] Add `P0EFTJanusTopologyLayerAlignmentGate`:
  - global topology is `S4 -> RP4` with antipodal `Z2` cover;
  - Big Bang / Big Crunch poles and their antipodal coincidence are explicit;
  - tunnel surgery is separated from the free antipodal quotient;
  - four physical sectors are `Z2_sheet x Z2_charge`;
  - cyclic `Z4` remains packaging unless order-4 monodromy is proved;
  - `RP4` Pin sign must not be imported from the `RP2`/Boy shadow.
- [x] Add `P0EFTJanusProjectiveTunnelInterface`:
  - unifies `S4 -> RP4` with tubular tunnel surgery;
  - derives the `aroundSigma` cycle transport into the existing Z2 holonomy path;
  - keeps cyclic `Z4` blocked until a lifted tunnel monodromy of order four is proved.
- [x] Add `P0EFTJanusAroundSigmaZ2CycleTransportGate`:
  - `aroundSigma` maps to the `Z2` generator;
  - no cyclic `Z4` monodromy is required for the active geometry.
- [x] Add `P0EFTJanusProjectiveTunnelCoverSurvivalGate`:
  - equivariant tubular surgery preserves the two-fold `S4 -> RP4` cover;
  - volume ratio is handled by the separate volume-ratio gate.
- [x] Add `P0EFTJanusProjectiveTunnelVolumeRatioGate`:
  - degree-two cover plus descended invariant measure gives cover/quotient ratio `2`;
  - ratio is unique by cover degree;
  - this does not infer an independent phenomenological sheet-split ratio.
- [x] Add `P0EFTJanusFormalModelReauditAfterTopologyCorrectionGate`:
  - resolved 2D tunnel shadow is `T2 -> Klein bottle`;
  - Boy surface remains unresolved projective shadow only;
  - active Z2/Sigma pure-math locks are closed; observational no-fit remains separate.
- [x] Add active `P0EFTJanusZ2TunnelCoreGate`.
- [x] Add active `P0EFTJanusZ2SigmaPureMathClosureAuditGate`.
- [x] Add active `P0EFTJanusZ2SigmaHardTheoremTargetRegistry`.
- [x] Add active `P0EFTJanusZ2SigmaObservationalRoadmapGate`:
  - pure math closed;
  - observational equation locks still open;
  - cyclic Z4 reactivation forbidden;
  - full no-fit cosmology remains false.
- [x] Add `P0EFTJanusZ2SigmaBackgroundBibliographyGate`:
  - Janus 2024 supplies projective/tunnel and bimetric FLRW ingredients;
  - junction/GHY/Israel literature supplies generic boundary machinery;
  - Einstein-Cartan/Holst literature supplies generic torsion blocks;
  - full projected Z2/Sigma background equations are not found in the literature.
- [x] Add `P0EFTJanusZ2SigmaBoundaryStressExtractionGate`:
  - extracts the formal `T_eff_ab` definition from the closed Sigma boundary action;
  - component blocks are declared for Cartan-GHY, Holst/Nieh-Yan, matter flux, tunnel junction and counterterm;
  - FLRW component reduction is still open.
- [x] Add `P0EFTJanusZ2SigmaThroatRadiusLawGate`:
    - imports generic FRW thin-shell wormhole throat-radius machinery;
    - records `R_Sigma(a)=a R0` only as a candidate ansatz;
    - keeps active Janus derivation of `R_Sigma(a)` open and forbids observational fitting.
  - [x] Add `P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate`:
    - records that topology alone underdetermines `R_Sigma(a)`;
    - declares `delta S_Sigma / delta R_Sigma(a) = 0` as the active no-fit equation;
    - keeps the equation unsolved until the boundary blocks are expanded.
  - [x] Add `P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate`:
    - declares `E_RSigma = E_CartanGHY + E_HolstNiehYan + E_flux + E_junction + E_ct = 0`;
    - records Israel/GHY/Brown-York bibliography support for the block strategy;
    - keeps all Janus/Sigma radial block reductions open.
  - [x] Add `P0EFTJanusZ2SigmaThroatRadiusBlockDependencyAuditGate`:
    - records that matter-flux and counterterm are the remaining blockers for `E_RSigma`;
    - keeps `R_Sigma(a)` unsolved until both missing radial blocks close.
  - [x] Add `P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGate`:
    - records that the variational equation and conditional embedding map are ready;
    - imports matter-flux transparency/projection, coupled radius-flux, and counterterm radial frontiers;
    - keeps the no-fit radius solution blocked by live upstream matter-flux and counterterm radial statuses;
    - reports the nearest unresolved radial block as diagnostic-only (`matter_flux` first in the current workspace).
  - [x] Wire active BAO runner through the strict `R_Sigma` input layer:
    - writes active Sigma/RP3 `unit_intrinsic_metric_q_ab_inputs.json`;
    - checks `rsigma_certificate_payload` and isotropic balance inputs without using Planck/LCDM/Z4 archives;
    - runs matter-flux transparency input, zero-component and radial-block gates before `E_matterFlux`;
    - reports the next physical target as `E_HolstNiehYan`, `E_matterFlux`, and `E_counterterm` radial derivation.
  - [ ] Derive non-Cartan `R_Sigma` radial terms:
    - derive Sigma torsion pullback and Immirzi profile for `E_HolstNiehYan(a)`;
    - derive active Sigma transparency or projected flux for `E_matterFlux(a)`;
    - prove counterterm residual exactness, integrate the primitive and reduce `E_counterterm(a)`;
    - then rerun the isotropic `R_Sigma` solver and propagate Cartan/GHY to the BAO runner.
  - [x] Wire the Holst/Nieh-Yan upstream into the BAO runner:
    - `torsion_pullback_on_sigma`, `immirzi_bulk_boundary_equation`,
      `immirzi_profile_of_a`, and `holst_nieh_yan_radial_block` now run before
      `R_Sigma` certificate assembly;
    - the active blocker is visible as `active_holst_nieh_yan_radial_inputs`,
      not an opaque missing radial term.
  - [x] Add strict Holst/Nieh-Yan radial term writer:
    - `rsigma_holst_nieh_yan_radial_term` writes `rsigma_E_HolstNiehYan.json`
      only from active `holst_nieh_yan_radial_inputs.json`;
    - it requires Sigma torsion pullback, FLRW irreducible torsion, Immirzi
      radial profile and Holst/Nieh-Yan radial reduction;
    - Planck/LCDM, archived Z4, observational H0/curvature and Holst-BAO scan
      provenance are rejected.
  - [x] Split Holst torsion readiness into Sigma pullback and FLRW irreducibles:
    - `flrw_irreducible_torsion_pullback` is now a runner step;
    - it requires `Sigma_torsion_pullback`, then trace/axial/tensor torsion
      component reduction;
    - no Holst radial term is emitted from a hardcoded torsion placeholder.
  - [x] Add algebraic FLRW torsion irreducible decomposition:
    - `flrw_irreducible_torsion_components` consumes active `q_ab` and
      `T^a_bc` pullback inputs;
    - it computes trace, totally antisymmetric and tensor torsion pieces;
    - it validates antisymmetry, nondegenerate metric and reconstruction
      residual before the FLRW irreducible gate can pass.
  - [x] Add Cartan torsion pullback component writer:
    - `torsion_pullback_components` consumes active coframe, `de^I`, and
      spin-connection pullback inputs;
    - it computes `T^I = de^I + omega^I_J wedge e^J` and converts it to
      `T^a_bc` through the inverse coframe;
    - it rejects non-antisymmetric connection/forms and forbidden provenance.
  - [x] Add torsionless coframe/connection baseline from unit q:
    - `coframe_connection_components_from_unit_q` writes a local orthonormal
      coframe and zero spin connection/exterior derivative from `q_ab`;
    - the resulting Cartan torsion is zero by construction;
    - the manifest is marked `torsionless_baseline_only`, not a nonzero Holst
      torsion solution.
  - [x] Add torsionless Holst/Nieh-Yan zero identity:
    - `holst_nieh_yan_radial_inputs_from_torsionless_identity` writes
      `E_HolstNiehYan(a)=0` only when all derived torsion components vanish;
    - the strict radial-term writer accepts this route without an Immirzi
      profile because the Nieh-Yan density is identically zero;
    - this is a baseline identity, not a nonzero Holst torsion branch.
  - [x] Wire the counterterm upstream into the BAO runner:
    - `counterterm_residual_channel_frontier`, one-form decomposition,
      integrability, extraction, density expansion and radial block now run
      before `R_Sigma` certificate assembly;
    - the active blocker is visible as residual channel/exactness/primitive
      status, not a missing opaque `rsigma_E_counterterm.json`.
  - [x] Split counterterm primitive integration out of residual extraction:
    - `counterterm_primitive_integration` now records the exactness-to-primitive
      step explicitly;
    - it requires residual one-form exactness, primitive residual cancellation,
      uniqueness up to constant, and no new counterterm freedom.
  - [x] Add nontransparent active-projection writer for `E_matterFlux`:
    - transparency still writes zero only after active Sigma transparency;
    - `rsigma_matter_flux_active_projection_radial_term` now accepts a derived
      active projected `E_matterFlux(a)` manifest;
    - non-Cartan status accepts either matter-flux route without fitting;
    - active projection is route-exclusive and cannot overwrite a derived
      transparency route.
  - [x] Add unified non-Cartan radial terms status:
    - reports readiness and blocker for `E_HolstNiehYan`, `E_matterFlux`, and
      `E_counterterm` in one place;
    - current blockers: `active_holst_nieh_yan_radial_inputs`,
      `active_Sigma_transparency_manifest`, and `tetrad_residual_channel`.
  - [x] Decouple `R_Sigma` certificate grid from Holst radial term:
    - `rsigma_a_grid_inputs.json` is now the preferred grid source;
    - fallback to `rsigma_E_HolstNiehYan.json` is retained only for compatibility;
    - current grid blocker is `active_a_grid_from_non_matter_FLRW_inputs`.
  - [x] Add solver-only collocation grid fallback:
    - `rsigma_solver_collocation_a_grid_input` writes `rsigma_a_grid_inputs.json`
      from validated active `q_ab`;
    - the manifest is marked `grid_role = solver_collocation_grid`;
    - it is explicitly not an observable, not a fit parameter, and not a derived
      FLRW scale-factor history.
  - [x] Add concrete active projection writer for `E_matterFlux(a)`:
    - consumes active `T_plus/minus`, tangent vectors, normals and radial
      variation weights;
    - computes `F_a^Z2Sigma` by tensor contraction;
    - writes `matter_flux_active_projection_radial_inputs.json` for the existing
      `rsigma_E_matterFlux` writer when those physical inputs are present.
  - [x] Centralize active matter-flux tensor contraction:
    - `janus_lab.z2_sigma_matter_flux.project_active_matter_flux_radial_values`
      computes `T^±_{μν} e_a^μ n_±^ν` and radial reduction;
    - the remaining blocker is the active input manifest with `T_pm`,
      tangents, normals and radial weights.
  - [x] Split `matter_flux_projection_components.json` into primitive active inputs:
    - active tunnel embedding geometry supplies tangents, normals and `eps_Z2`;
    - active bulk stress on Sigma supplies `T_plus/minus`;
    - active radial-variation weights supply `deltaX_RSigma`;
    - the writer emits projection components only when all three are present.
  - [x] Add active bulk-stress-on-Sigma perfect-fluid writer:
    - consumes sector `rho/p`, covariant metrics and contravariant four-velocities;
    - computes `T_munu=(rho+p)u_mu u_nu+p g_munu`;
    - writes `bulk_stress_on_sigma_inputs.json` for the matter-flux projection path.
  - [x] Split sector perfect-fluid inputs into primitives:
    - density/pressure on Sigma;
    - covariant metric on Sigma;
    - contravariant four-velocity on Sigma;
    - the assembler writes `sector_perfect_fluid_on_sigma_inputs.json` only when
      all three are active-derived.
  - [x] Derive sector four-velocity from active time direction:
    - consumes sector covariant metrics and timelike direction fields;
    - normalizes `u` with `g_munu u^mu u^nu = -1`;
    - writes `sector_four_velocity_on_sigma_inputs.json`.
  - [x] Add strict counterterm radial density variation writer:
    - consumes explicit `sqrt|h|`, `partial_R sqrt|h|`, `L_ct`, and
      `partial_R L_ct`;
    - computes `E_counterterm = partial_R(sqrt|h| L_ct)`;
    - rejects fitted counterterm coefficients and writes `rsigma_E_counterterm`
      only when all active density-variation inputs are present.
  - [x] Derive counterterm geometry factors from active unit `q_ab`:
    - for `h_ab = R_Sigma^2 q_ab`, derives
      `sqrt|h| = R_Sigma^3 sqrt(det q)`;
    - derives `partial_R sqrt|h| = 3 R_Sigma^2 sqrt(det q)`;
    - keeps `L_ct` and `R_Sigma(a)` as required physical inputs.
  - [x] Add counterterm radial density variation input writer:
    - combines geometry factors with active `R_Sigma`, `L_ct`, and
      `partial_R L_ct` profiles;
    - writes `counterterm_radial_density_variation_inputs.json`;
    - blocks on `counterterm_lct_radial_profile` until the active density
      profile is derived or supplied.
  - [x] Mark `R_Sigma` payloads as templates until solved:
    - `rsigma_certificate_payload.json` carries `rsigma_payload_is_template = true`;
    - the isotropic balance solver clears that marker and emits
      `active_no_fit_solution` only after solving `E_RSigma = 0`.
  - [x] Forbid template payload propagation into embedding/curvature:
    - `rsigma_solution_to_embedding_curvature_branch` now requires
      `active_no_fit_solution`;
    - conditional/template payloads cannot write embedding, curvature, H0 or
      curvature-radius normalization manifests.
  - [x] Expose non-matter FLRW component assembly in the BAO runner:
    - runs `cartan_ghy_component`, `holst_nieh_yan_component`,
      `counterterm_component`, and `flrw_non_matter_inputs_assembler` before
      `rsigma_a_grid_input`;
    - current upstream blockers are active `DeltaK_s/tau`, Holst/Nieh-Yan FLRW
      reduction, and counterterm FLRW/radial reduction.
  - [x] Expose strict Cartan-GHY upstream chain in the BAO runner:
    - runs FLRW extrinsic-curvature grid builder/writer, jump builder,
      `cartan_ghy_deltaK_input`, background scalar inputs, and background scalar
      manifest writer before `cartan_ghy_component`;
    - current blockers are active tunnel embedding/`K_ab(a)` and active
      `H0/R_curv` normalization, not hidden component placeholders.
  - [x] Allow strict `second_embedding -> K_s/K_tau` reduction:
    - `active_embedding_to_flrw_extrinsic_curvature_input_gate` now computes
      FLRW extrinsic-curvature scalars from active `second_embedding_plus/minus`,
      tangent frames, Christoffels, normals, and spatial inverse metric;
    - it still accepts explicit active `K_*` fields when present;
    - it remains blocked until the active embedding manifest exists.
  - [x] Preserve optional second-form data through the `R_Sigma` certificate bridge:
    - strict certificates may carry `second_embedding_plus/minus`, `tau_index`,
      and `spatial_indices`;
    - the embedding/curvature bridge copies those fields into
      `active_tunnel_embedding_geometry_inputs.json`;
    - this lets a future solved certificate feed Cartan-GHY without a separate
      precomputed `K_*` fixture.
  - [x] Tighten `P0EFTJanusZ2SigmaRSigmaSolutionToEmbeddingCurvatureBranchGate`:
    - bridge writes now require matter-flux and counterterm blocks, the throat solution certificate, and `embedding_unblocked_by_radius_solution`;
    - a complete certificate alone cannot write embedding or curvature manifests.
  - [x] Add `P0EFTJanusZ2SigmaCartanGHYRadialBlockGate`:
    - reduces `E_CartanGHY` structurally from `delta_RSigma[sqrt(|h|) K]`;
    - keeps `E_CartanGHY(a)` blocked on `R_Sigma(a)` and `X_±(a)`.
  - [x] Add `P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate`:
    - declares `E_HolstNiehYan` as radial variation of the Sigma torsion/Nieh-Yan pullback;
    - keeps its scale-factor form blocked on torsion pullback and Immirzi profile.
  - [x] Add `P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGate`:
    - records the thin-shell transport `R_Sigma(a)` plus gauge equations to `X_+/-`;
    - keeps transport blocked until the no-fit throat-radius law is solved.
  - [x] Add `P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGate`:
    - closes the conditional thin-shell map `R_Sigma(a) -> X_+/-`;
    - keeps unconditional embedding blocked until the active throat-radius law is solved.
  - [x] Add `P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate`:
    - imports dynamic-shell kinematics for `R_Sigma(a) -> X_±(a)`;
    - keeps active embedding blocked until `R_Sigma(a)` is solved from the radial variational equation.
  - [x] Add `P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate`:
    - records that the conditional thin-shell embedding map is ready;
    - imports live radius-to-embedding and embedding-from-radius statuses without importing the throat-radius frontier cycle;
    - keeps active `X_+/- (a)`, tangent frames and unit normals blocked on `R_Sigma(a)`;
    - now also requires the throat-radius solution certificate and `embedding_unblocked_by_radius_solution` before active embedding readiness can pass.
  - [x] Add `P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate`:
    - records `E_a_pm^mu = partial_a X_pm^mu`;
    - keeps tangent frames blocked until active `X_+/- (a)` is derived.
  - [x] Add `P0EFTJanusZ2SigmaTangentNormalOrientationGate`:
    - imports thin-shell tangent frame, unit normal and orientation conventions;
    - gets `epsilon_Z2=-1` from projective gluing, while active frames and unit normals remain open.
  - [x] Add `P0EFTJanusZ2SigmaCoframeConnectionPullbackGate`:
    - imports first-order coframe/spin-connection pullback machinery;
    - keeps `X_Sigma^*(e)` and `X_Sigma^*(omega)` blocked on active embedding;
    - marks Z2-oriented pullback transport ready from the projective sign.
  - [x] Add `P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGate`:
    - closes the standard differential-form/coframe/connection pullback formulae;
    - imports live active-embedding and tangent-normal orientation statuses;
    - keeps actual coframe and spin-connection pullbacks blocked on active embedding, tangent frames and unit normals.
  - [x] Add `P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate`:
    - imports differential-form pullback and Cartan first structure equation;
    - records Cartan torsion and `X_Sigma^*(T^I)` pullback formula subchannels as partial-ready;
    - imports live coframe/connection pullback readiness;
    - keeps Sigma torsion pullback blocked on embedding, coframe/connection pullbacks and FLRW irreducible split.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxRadialBlockGate`:
    - imports the normal-tangent flux term `T_munu e_a^mu n^nu`;
    - keeps `E_matterFlux` blocked until transparency or active flux is derived.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxRouteDecisionGate`:
    - declares the transparency-vs-active-projection fork;
    - forbids choosing the matter-flux route by observational fit.
  - [x] Add `p0_eft_janus_z2_sigma_matter_flux_route_investigation`:
    - compares transparency `F_a=0` against coupled `R_Sigma(a)` + embedding + flux;
    - selects the coupled constructive path while transparency remains unproved;
    - records that the negative sector is gravitational/Z2-signed, not an assumed
      thermodynamic negative-density shortcut.
  - [x] Add `P0EFTJanusZ2SigmaEquivariantFluxCancellationGate`:
    - declares the Janus/Z2 route to transparency through embedding equivariance,
      normal reversal, tangent transport, and stress equivariance;
    - keeps `F_a=0` blocked until active embedding and `T_- = tau_* T_+` are derived.
  - [x] Add `p0_eft_janus_z2_sigma_sector_metric_time_direction_from_unit_throat_chart`
    and `p0_eft_janus_z2_sigma_flow_tangency_from_embedding_velocity`:
    - materializes the unit-throat sector metric/time direction and four-velocity;
    - reduces the perfect-fluid tangency test to the active embedding geometry
      manifest needed for `u.n=0` and `e.n=0`.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxFrontierGate`:
    - records transparency and active-projection routes as the exact flux frontier;
    - imports live transparency, active-projection, route-decision and radial-block statuses;
    - keeps full transparency open, but the perfect-fluid tangential route now
      reduces the radial `E_matterFlux` block without claiming transparency.
  - [x] Add `P0EFTJanusZ2SigmaFluxProjectionDomainGate`:
    - records Sigma and Z2 coorientation as available from the projective tunnel;
    - keeps the flux projection domain blocked on resolved frame bundle,
      active `X_±(a)`, tangent traces and unit normals;
    - does not derive transparency, active flux or `E_matterFlux`.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxTransparencyReadinessGate`:
    - records current and stress-flux transparency criteria from thin-shell literature;
    - keeps transparency blocked on active embedding, Sigma normals, normal current and bulk-stress cancellation.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxRadiusAcyclicityGate`:
    - forbids using `F_a[X_+/-[R_Sigma]]` as an independent radius source;
    - requires independently derived transparency, a coupled radius-flux system,
      or the non-circular perfect-fluid tangential zero route.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxSystemGate`:
    - declares coupled unknowns `R_Sigma(a)`, `X_+/-[R_Sigma]`, and `F_a^Z2Sigma(a)`;
    - imports live function-space and well-posedness frontiers;
    - keeps the coupled system blocked until well-posedness and solution are derived.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxWellPosednessGate`:
    - declares the local existence/uniqueness/continuous-dependence obligations;
    - keeps `coupled_system_well_posed = false` until those obligations are proved.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGate`:
    - declares the `R_Sigma`, flux, embedding-trace, boundary-data, and gauge-slice spaces;
    - keeps the analytic map/trace/Fredholm obligations open.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxTraceRegularityGate`:
    - declares trace maps for `X_+/-[R_Sigma]`, `n_mu`, `e_a^mu`, and `T_pm`;
    - keeps `T_pm e_a^mu n_mu` product well-definedness open.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevIndexGate`:
    - records `dim(Sigma)=3`, trace loss `1/2`, and candidate `s_bulk >= 3`;
    - keeps trace/product/normal-frame threshold proofs open.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGate`:
    - closes trace/product thresholds using standard Sobolev trace/multiplication routes;
    - keeps normal/tangent frame trace support open.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGate`:
    - declares tangent/normal frame traces as consequences of regular co-oriented embedding;
    - keeps their trace continuity/support open until transported from embedding regularity.
  - [x] Add `P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGate`:
    - states conditional transport from regular co-oriented nondegenerate embedding to frame traces;
    - consumes the flux-domain gate so Z2/Sigma coorientation is no longer a live blocker;
    - keeps the transport blocked until embedding regularity/equivariance closes.
  - [x] Add `P0EFTJanusZ2SigmaPlusMinusSpinorBundleDataGate`:
    - imports Spin/Pin obstruction machinery and the RP4 Pin+ result;
    - declares `S_+ -> M_+` and `S_- -> M_-`;
    - indexes `ResolvedTunnelPinLiftGate` as the upstream frontier;
    - keeps resolved-tunnel Pin lift and active bundle data open.
  - [x] Add `P0EFTJanusZ2SigmaBoundarySpinorRestrictionGate`:
    - imports generic hypersurface spinor restriction;
    - declares `psi_+|_Sigma`, `psi_-|_Sigma` and the boundary spinor pair;
    - keeps the restriction blocked on active Sigma embedding and spinor bundles.
  - [x] Add `P0EFTJanusZ2SigmaSpinorBoundaryProjectionMapGate`:
    - imports APS and local Dirac-boundary projector machinery;
    - declares `P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, n_Z2, APS/Pin data)`;
    - records Z2 coorientation as partial-ready from the flux-domain gate;
    - records Sigma APS/Pin as closed upstream;
    - keeps boundary spinor data and unit normal Clifford action blocked on active embedding/bundles;
    - forbids fitted boundary phases and keeps idempotence/self-adjointness open.
  - [x] Add `P0EFTJanusZ2SigmaSpinorBundleProjectionGate`:
    - imports spinor-bundle, boundary-restriction and APS-boundary machinery;
    - declares `psi_Sigma^Z2 = P_Z2Sigma(psi_+|_Sigma, psi_-|_Sigma, APS/Pin data)`;
    - keeps active plus/minus spinor bundle and boundary-projection data open.
  - [x] Add `P0EFTJanusZ2SigmaSpinorProjectionReadinessGate`:
    - closes generic hypersurface spinor restriction and APS/local projection formulae;
    - keeps active plus/minus projection blocked on tunnel Pin lift, boundary spinors and idempotent Z2/Sigma projection map.
  - [x] Add `P0EFTJanusZ2SigmaProjectedDiracActionReductionGate`:
    - imports first-order curved Dirac action and Holst/fermion coupling machinery;
    - declares `S_D^Z2Sigma = P_Z2Sigma(S_D,+, S_D,-; psi_Sigma^Z2)`;
    - forbids fitted effective masses, boundary phases and chiral angles.
  - [x] Add `P0EFTJanusZ2SigmaProjectedDiracActionReadinessGate`:
    - closes the standard curved-Dirac/Holst-fermion formulae;
    - keeps the active projected action blocked on coframe/connection pullbacks and Z2/Sigma spinor projection.
  - [x] Add `P0EFTJanusZ2SigmaPlusMinusDiracMatterActionGate`:
    - imports curved Dirac action and Holst/fermion coupling context;
    - keeps plus/minus matter actions blocked on coframe/connection and spinor projection data.
  - [x] Add `P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate`:
    - imports Dirac U(1) Noether-current machinery;
    - declares `J_Z2Sigma^mu = P_Z2Sigma(J_+^mu, J_-^mu; psi_Sigma^Z2)`;
    - keeps projected current blocked until the projected Dirac action is reduced.
  - [x] Add `P0EFTJanusZ2SigmaReflectingSpinorBoundaryCurrentGate`:
    - records the reflecting/MIT-bag route to `J_n=0`;
    - keeps it blocked until the active spinor projector, normal Clifford action and zero-leakage condition are derived without a free boundary phase.
  - [x] Add `P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate`:
    - projects the active Dirac current on Sigma normals;
    - declares `J_n^Z2Sigma = J_n^+ + eps_Z2 J_n^-`;
    - keeps `J_n^Z2Sigma=0` blocked until current/normals or the reflecting spinor boundary-current route are derived.
  - [x] Add `P0EFTJanusZ2SigmaBulkStressNormalFluxCancellationGate`:
    - declares `F_a^Z2Sigma = F_a^+ + eps_Z2 F_a^-`;
    - imports thin-shell momentum-flux machinery;
    - keeps zero-flux/Z2 cancellation blocked on active bulk stresses and normals.
  - [x] Add `P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate`:
    - imports generic Dirac Noether current structure;
    - keeps `J_+` and `J_-` blocked on active plus/minus matter actions.
  - [x] Add `P0EFTJanusZ2SigmaNormalMatterCurrentGate`:
    - imports generic current normal-projection criterion;
    - keeps `J_n^Z2Sigma=0` blocked on active currents and Sigma normals.
  - [x] Add `P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate`:
    - records the Dirac Noether current and normal projection formulae;
    - keeps `J_n^Z2Sigma=0` blocked on active normals and projected Dirac currents.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxTransparencyGate`:
    - declares sufficient conditions for `F_a^Z2Sigma=0`;
    - imports live normal-current, projected Dirac normal-current and bulk-stress flux frontiers;
    - keeps transparency open until normal current or Z2 flux cancellation is derived.
  - [x] Add `P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate`:
    - declares the non-transparent branch `F_a^± = T^±_munu e_a^mu n_±^nu`;
    - keeps active flux blocked on bulk stresses and active embedding data.
  - [x] Add `P0EFTJanusZ2SigmaBulkStressOfAGate`:
    - declares `T^±_munu(a)` from sector perfect fluids plus Holst torsion stress;
    - keeps bulk stress blocked on active sector densities/pressures and torsion stress.
  - [x] Add `P0EFTJanusZ2SigmaSectorDensityPressureOfAGate`:
    - imports FLRW perfect-fluid continuity per sector;
    - keeps `rho_±(a), p_±(a)` blocked on derived equations of state and normalizations.
  - [x] Add `P0EFTJanusZ2SigmaHolstTorsionStressOfAGate`:
    - declares `T_HolstTorsion_munu(a)` by metric variation of the Holst/torsion action;
    - keeps the stress blocked on the active torsion solution and Immirzi profile.
  - [x] Add `P0EFTJanusZ2SigmaImmirziProfileOfAGate`:
    - imports dynamic Barbero-Immirzi scalar-field/Nieh-Yan literature;
    - keeps `gamma_Immirzi(a)` blocked on the bulk equation, Sigma boundary condition and Z2/Sigma projection.
  - [x] Add `P0EFTJanusZ2SigmaImmirziBulkBoundaryEquationGate`:
    - imports scalar-Immirzi Holst/Nieh-Yan variation structure;
    - keeps `E_gamma=0` and `B_gamma^Sigma=0` blocked on torsion pullback and spinor source.
  - [x] Add `P0EFTJanusZ2SigmaTorsionFieldSolutionOfAGate`:
    - imports the generic Sciama-Kibble/Cartan spin-torsion constraint;
    - keeps `T_Z2Sigma(a)` blocked on spin current, boundary torsion source and Immirzi profile.
  - [x] Add `P0EFTJanusZ2SigmaSpinCurrentOfAGate`:
    - imports canonical spin tensor and Dirac axial-current structure;
    - keeps active spin current blocked on fermion distribution, spin polarization and Z2/Sigma projection.
  - [x] Add `P0EFTJanusZ2SigmaFermionDistributionOfAGate`:
    - declares Dirac-gas and Weyssenhoff-fluid routes from the literature;
    - keeps active distributions blocked until the route and plus/minus projections are action/topology-derived.
  - [x] Add `P0EFTJanusZ2SigmaDiracThermalOccupationOfAGate`:
    - imports Fermi-Dirac occupation and phase-space moment machinery;
    - keeps `f_pm(q,a)` blocked on normalization, mass/temperature, regime and chemical potentials.
  - [x] Add `P0EFTJanusZ2SigmaDiracChemicalPotentialOfAGate`:
    - declares number-constraint inversion for `mu_pm(a)`;
    - keeps chemical potentials blocked on `N_pm`, mass/temperature and regime;
    - forbids chemical-potential fitting.
  - [x] Add `P0EFTJanusZ2SigmaDiracDegeneracyFactorGate`:
    - declares internal/spin degeneracy factors `g_+`, `g_-`, `g_Z2Sigma`;
    - keeps degeneracies blocked on spinor bundles, projection and route selection;
    - forbids degeneracy fitting.
  - [x] Add `P0EFTJanusZ2SigmaDiracEquationOfStateOfAGate`:
    - imports kinetic Fermi-gas `rho_pm(a), p_pm(a)` integrals;
    - keeps active equations of state blocked on distribution, regime and mass/temperature laws.
  - [x] Add `P0EFTJanusZ2SigmaKineticMomentFluidClosureGate`:
    - imports kinetic stress-energy moment `T_munu[f]`;
    - keeps FLRW fluid reduction blocked on projected distributions and isotropy/no-anisotropic-stress.
  - [x] Add `P0EFTJanusZ2SigmaDistributionIsotropyAnisotropicStressGate`:
    - records `f_pm(q_vec,a)=f_pm(|q|,a)` and `pi_ij=T_ij-p h_ij`;
    - keeps projected FLRW closure blocked until plus/minus isotropy and zero projected anisotropic stress are derived.
  - [x] Add `P0EFTJanusZ2SigmaDiracFermiDiracIsotropyGate`:
    - imports the standard Fermi-Dirac radiality argument;
    - keeps isotropy blocked on radial plus/minus dispersion and Z2/Sigma projection-preservation.
  - [x] Add `P0EFTJanusZ2SigmaDiracRadialEnergyDispersionGate`:
    - imports `epsilon_pm(q,a)=sqrt(q^2+a^2 m_pm(a)^2)`;
    - keeps radiality blocked until scalar mass laws and FLRW momentum frames are derived.
  - [x] Add `P0EFTJanusZ2SigmaRadialOccupationProjectionGate`:
    - records the rotation-equivariance condition for `P_Z2Sigma`;
    - keeps projected radial occupation blocked until the active throat projection is shown to preserve radiality.
  - [x] Add `P0EFTJanusZ2SigmaFLRWMomentumFrameGate`:
    - imports the standard FLRW comoving momentum frame `q_i=a p_hat_i`;
    - keeps the projected momentum frame blocked on active plus/minus coframe pullbacks.
  - [x] Add `P0EFTJanusZ2SigmaDiracScalarMassLawGate`:
    - imports the generic curved-space Dirac scalar mass-term fact;
    - keeps plus/minus mass laws blocked until derived from the projected Dirac action.
  - [x] Add `P0EFTJanusZ2SigmaDiracMassTermFromActionGate`:
    - declares extraction of `m_±(a)` as the coefficient of `psibar_± psi_±`;
    - keeps extraction blocked until the plus/minus projected Dirac actions are reduced.
  - [x] Add `P0EFTJanusZ2SigmaPlusMinusDiracActionLocalReductionGate`:
    - declares the local kinetic, mass-bilinear and axial-torsion decomposition;
    - keeps reduction blocked until plus/minus matter actions are ready.
  - [x] Add `P0EFTJanusZ2SigmaResolvedTunnelPinLiftGate`:
    - declares the resolved tunnel frame-bundle Pin lift and plus/minus restrictions;
    - indexes `ResolvedTunnelFrameBundleGate` as the upstream frontier;
    - keeps spinor bundles blocked until the active resolved-tunnel lift is derived.
  - [x] Add `P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGate`:
    - records rank, topological embedding, regular radius and Z2-equivariance checks;
    - keeps smooth-throat closure blocked until active `X_+/-` are derived.
  - [x] Add `P0EFTJanusZ2SigmaSmoothEmbeddedThroatGate`:
    - records embedded-submanifold prerequisites for the Sigma throat;
    - keeps collars blocked until active embedding, regular radius, rank and Z2 equivariance are derived.
  - [x] Add `P0EFTJanusZ2SigmaCollarTubularNeighborhoodGate`:
    - records collar/tubular-neighborhood bibliography around the Sigma throat;
    - keeps the atlas blocked until Sigma smoothness, normal bundle and collars are derived.
  - [x] Add `P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGate`:
    - records collar/tubular/gluing bibliography for the resolved tunnel atlas;
    - keeps the frame bundle blocked until collars and transition maps are derived.
  - [x] Add `P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGate`:
    - declares `T M_res` and `F(M_res)` after tubular replacement;
    - keeps the Pin lift blocked until the smooth atlas/tangent bundle are derived.
  - [x] Add `P0EFTJanusZ2SigmaFermionRouteSelectionGate`:
    - selects the Dirac/spinorial route from the active Sigma spinor-variation channel;
    - keeps Weyssenhoff as coarse-graining only, not a primitive fitted route.
  - [x] Add `P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate`:
    - imports conserved Dirac charge integrals on hypersurfaces;
    - declares `N_Z2Sigma = P_Z2Sigma(N_+, N_-; psi_Sigma^Z2)`;
    - keeps charges blocked on projected current, spinor projection and no-leak guards.
  - [x] Add `P0EFTJanusZ2SigmaDiracFermionNumberDensityOfAGate`:
    - imports conserved Dirac number-current dilution `n_pm(a)=N_pm/a^3`;
    - keeps `N_+`, `N_-` and projected Z2/Sigma density blocked on action/topology.
  - [x] Add `P0EFTJanusZ2SigmaDiracNumberNormalizationGate`:
    - declares Noether-charge integrals for `N_+`, `N_-` and projected throat charge;
    - keeps charge values blocked until active spinor boundary data/topology fixes them.
  - [x] Add `P0EFTJanusZ2SigmaBaryonNumberDensityNoetherVolumeGate`:
    - declares `n_b0_Z2Sigma = N_b,Z2Sigma / V0,Z2Sigma`;
    - keeps `baryon_number_density0_m3_Z2Sigma` blocked until projected Noether charge
      and active spatial volume are derived;
    - forbids Planck/LCDM, archived Z4 and phenomenological BAO-fit provenance.
  - [x] Add `P0EFTJanusZ2SigmaSpatialVolumeProjectiveSliceGate`:
    - declares `V0_Z2Sigma = (1/2) integral_cover sqrt(det h_cover) d^3x`;
    - specializes the closed projective slice to `V0_Z2Sigma = pi^2 R_curv^3`;
    - requires closed projective spatial branch `k_Z2Sigma = +1`;
    - keeps volume values blocked until active curvature radius/spatial branch
      data are supplied with active provenance.
  - [x] Add `P0EFTJanusZ2SigmaRP3SpatialSliceCurvatureSignGate`:
    - conditionally writes `k_Z2Sigma = +1` from active `S3 -> RP3` spatial
      slice provenance;
    - keeps `R_curv_Z2Sigma` and `omega_k_Z2Sigma` blocked.
  - [x] Add `P0EFTJanusZ2SigmaRP3SpatialSliceInputWriterFromProjectiveFoliationGate`:
    - writes `rp3_spatial_slice_inputs.json` only from active projective
      foliation data;
    - requires FLRW slices to be identified with antipodal `S3 -> RP3` leaves.
  - [x] Add `P0EFTJanusZ2SigmaProjectiveFoliationCompatibilityGate`:
    - records that generic `S4` latitude leaves are antipodal-paired;
    - blocks single-leaf `RP3` inference until an active invariant-leaf time
      gauge is derived.
  - [x] Add `P0EFTJanusZ2SigmaProjectiveSpatialSliceTopologyBranchGate`:
    - distinguishes invariant-leaf `RP3` from paired-leaf representative `S3`;
    - writes `k_Z2Sigma = +1` only after active time-gauge leaf action is supplied;
    - keeps `R_curv_Z2Sigma` and `omega_k_Z2Sigma` open.
  - [x] Add `P0EFTJanusZ2SigmaSignedCoverTimeCoordinateFromProjectiveTunnelGate`:
    - derives the active signed cover-time coordinate from the S4 projective
      tunnel pole axis;
    - writes `signed_cover_time_coordinate_inputs.json` with antipodal pullback
      `minus_self`;
    - uses no Planck/LCDM background, archived Z4, or observational time-gauge
      fit.
  - [x] Add `P0EFTJanusZ2SigmaSignedCoverTimeParityGate`:
    - narrows the upstream blocker to
      `outputs/active_z2_sigma/signed_cover_time_coordinate_inputs.json`;
    - maps antipodal pullback `plus_self` to even parity and `minus_self` to odd
      parity;
    - forbids Planck/LCDM background, archived Z4 reuse, and observational
      time-gauge fitting.
  - [x] Add `P0EFTJanusZ2SigmaTimeGaugeLeafActionInputWriterGate`:
    - maps active antipodal time parity to leaf action type;
    - forbids observational time-gauge fitting.
  - [x] Add `P0EFTJanusZ2SigmaBackgroundCurvatureBranchInputsAssemblerGate`:
    - merges active `H0_Z2Sigma`, `k_Z2Sigma`, and `R_curv_Z2Sigma` manifests
      into `background_curvature_branch_inputs.json`;
    - keeps the active curvature radius as the remaining embedding/throat-scale
      input before `omega_k_Z2Sigma` can be evaluated.
  - [x] Add `P0EFTJanusZ2SigmaScaleFreeOmegaKFromCurvatureScaleGate`:
    - computes `omega_k_Z2Sigma = -k/(H0 R_curv/c)^2` for scale-free DESI BAO;
    - avoids a dimensional observational `H0` in the BAO ratio path;
    - keeps `H0_R_curv_over_c_Z2Sigma` as an active dimensionless curvature
      scale obligation.
  - [x] Add `P0EFTJanusZ2SigmaSpatialVolumeInputWriterFromCurvatureBranchGate`:
    - consumes active `background_curvature_branch_inputs.json`;
    - converts `R_curv_Z2Sigma_Mpc` to `R_curv_Z2Sigma_m`;
    - requires `k_Z2Sigma = +1`;
    - writes `spatial_volume_projective_slice_inputs.json` only from active provenance;
    - records that `H0_R_curv_over_c_Z2Sigma` alone cannot determine physical volume.
  - [x] Clarify dimensional H0/R_curv blockers:
    - `BackgroundAtomicInputWriterGates` records that `H0_R_curv_over_c_Z2Sigma`
      is insufficient to determine dimensional `H0_Z2Sigma`;
    - `BackgroundCurvatureRadiusInputWriterGate` records the matching
      dimensional `R_curv_Z2Sigma` blocker;
    - live missing artifacts are
      `outputs/active_z2_sigma/background_H0_normalization_inputs.json` and
      `outputs/active_z2_sigma/background_curvature_radius_normalization_inputs.json`.
  - [x] Add `P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate`:
    - validates `projected_baryon_number_charge_Z2Sigma` only after projected
      Dirac current and charge-boundary projection readiness;
    - preflights the live Dirac charge-boundary projection gate, so fixture/source
      manifests cannot self-certify the projected baryon charge;
    - forbids free projection weights and observational baryon fits.
  - [x] Add `P0EFTJanusZ2SigmaDiracHolstVertexOfAGate`:
    - imports the generic Holst-fermion torsion-mediated four-fermion vertex;
    - keeps matrix elements blocked on active torsion, spin current, Immirzi profile and Sigma projection.
  - [x] Add `P0EFTJanusZ2SigmaDiracThermalCrossSectionOfAGate`:
    - imports generic `<sigma v>` thermal averaging and Gondolo-Gelmini relativistic averaging;
    - keeps cross sections blocked on active matrix elements, phase-space measures and projection.
  - [x] Add `P0EFTJanusZ2SigmaDiracInteractionRateOfAGate`:
    - imports `Gamma_pm(a)=n_bath,pm(a)<sigma v>_pm(a)` as generic kinetic structure;
    - keeps rates blocked on active bath densities, cross sections and Z2/Sigma projection.
  - [x] Add `P0EFTJanusZ2SigmaDiracMassTemperatureLawOfAGate`:
    - imports momentum redshift and relativistic decoupled temperature scaling as generic machinery;
    - keeps massive regime, decoupling scale and projected mass/temperature law blocked on active derivation.
  - [x] Add `P0EFTJanusZ2SigmaDiracRegimeSelectionGate`:
    - declares `m_pm/T_dec_pm` as the relativistic/massive/semi-relativistic criterion;
    - keeps regime selection blocked until active masses and decoupling temperatures are derived.
  - [x] Add `P0EFTJanusZ2SigmaDiracDecouplingConditionGate`:
    - imports `Gamma_pm(a_dec)=H_Z2Sigma(a_dec)` as the standard freeze-out condition;
    - keeps decoupling blocked until `Gamma_+/- (a)` and `H_Z2Sigma(a)` are derived.
  - [x] Add `P0EFTJanusZ2SigmaTunnelJunctionRadialBlockGate`:
    - reduces `E_tunnelJunction` structurally from the Lanczos-Israel jump residual;
    - keeps its scale-factor form blocked on `DeltaK_s(a)`, `DeltaK_tau(a)` and source partition.
  - [x] Add `P0EFTJanusZ2SigmaCountertermRadialBlockGate`:
    - declares radial variation of the unique Sigma counterterm;
    - keeps reduction blocked until explicit `L_ct` is expanded.
  - [x] Add `P0EFTJanusZ2SigmaCountertermLocalDensityBasisGate`:
    - declares the allowed local active basis for `L_ct`;
    - keeps expansion blocked until the explicit unique density is derived.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradResidualChannelGate`:
    - isolates the coframe/tetrad residual coefficient `R_e`;
    - imports the live tetrad-variation transport readiness frontier;
    - records the metric residual subchannel as partial-only;
    - blocks until `delta e` is transported to `delta h`, `delta K` and torsion data.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradVariationTransportGate`:
    - declares `delta e -> delta h`, `delta e -> delta K`, and torsion-pullback transports;
    - imports live metric, extrinsic-curvature and torsion-pullback transport statuses;
    - blocks `R_e` until those transports are derived.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGate`:
    - closes the algebraic `delta e -> delta h_ab` transport;
    - leaves `delta K` and torsion-pullback transports open.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGate`:
    - declares `K_ab = e_a e_b nabla n` and the `delta K` variation channels;
    - imports live active-embedding, frame-trace and connection-variation statuses;
    - keeps `delta e -> delta K` blocked on embedding, frame traces and connection variation.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackVariationTransportGate`:
    - records `delta_e T^I = D_omega(delta e^I)` in the independent-connection branch;
    - imports live torsion-pullback and oriented pullback/variation commutation statuses;
    - keeps Sigma torsion pullback and allowed-basis expansion open.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradTorsionPullbackReadinessGate`:
    - records oriented pullback commutation plus ambient Cartan and Sigma pullback torsion formulae as closed;
    - keeps active embedding, coframe/connection pullback, Sigma torsion pullback and FLRW irreducible basis open.
  - [x] Add `P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGate`:
    - aggregates metric, extrinsic-curvature and torsion-pullback tetrad transports;
    - records metric transport closed and keeps `R_e` blocked on `delta K` and torsion.
  - [x] Add `P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGate`:
    - isolates the spin-connection residual coefficient `R_omega`;
    - records fixed-embedding pullback commutation as partial-only via the connection transport gate;
    - blocks until `delta omega` is fully transported through torsion/Nieh-Yan boundary data and `R_omega` is explicit.
  - [x] Add `P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGate`:
    - records `delta_omega T^I = delta omega^I_J wedge e^J`;
    - imports live fixed-embedding connection pullback and torsion-pullback statuses;
    - records fixed-embedding pullback commutation as partial-only;
    - blocks until pullback and Nieh-Yan variation transport are proved on Sigma.
  - [x] Add `P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGate`:
    - proves the channel split condition `delta_omega X_Sigma = 0`;
    - keeps embedding variation isolated in the `R_X` channel.
  - [x] Add `P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate`:
    - proves fixed-map commutation of `delta_omega` with `X_Sigma^*`;
    - leaves Z2-oriented commutation as the remaining pullback variation blocker.
  - [x] Add `P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate`:
    - fixes `epsilon_Z2=-1` from projective-tunnel sheet exchange;
    - forbids fitted/manual plus-minus normal signs.
  - [x] Add `P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate`:
    - imports thin-shell orientation conventions;
    - transports the fixed Z2 normal sign into oriented pullback commutation.
  - [x] Add `P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGate`:
    - declares the fixed-embedding branch `delta_omega X_Sigma = 0`;
    - imports live active-embedding, coframe/connection pullback and oriented-commutation statuses;
    - blocks until pullback/variation commutation and Z2 orientation are proved.
  - [x] Add spinor, embedding and matter-flux residual channel gates:
    - isolates `R_psi`, `R_X` and `R_matter`;
    - matter-flux now imports the live active matter-flux frontier;
    - keeps all three blocked until their coefficients are explicit in the active basis.
  - [x] Add `P0EFTJanusZ2SigmaSpinorSolderingEquivarianceFromBoundaryVariationGate`:
    - reduces `psi_- = U_Z2 psi_+` to the projected Dirac boundary spinor
      residual, instead of assuming a free spinor phase or MIT condition;
    - current blocker is `spinor_soldering_boundary_variation_residual`.
  - [x] Add `P0EFTJanusZ2SigmaSpinorQuotientDescentEquivarianceGate`:
    - records the quotient/descent route for `psi_- = U_Z2 psi_+`;
    - blocks on `resolved_tunnel_Pin_lift_for_spinor_descent`;
    - keeps legacy Z4 monodromy and independent plus/minus spinors forbidden.
  - [x] Refine the counterterm residual attack order:
    - `CountertermResidualChannelFrontierGate` now reports `tetrad` as the
      nearest diagnostic residual channel;
    - `CountertermTetradVariationTransportReadinessGate` now reports
      `delta_e_to_delta_K` as the nearest missing subgate;
    - Lean proves that missing extrinsic-curvature variation transport blocks
      parent tetrad transport readiness.
  - [x] Add formula-only `delta_e -> delta_K` structural variation:
    - records
      `delta K_ab = -delta n_mu A_ab^mu - n_mu(delta X'' + delta Gamma ee + Gamma delta(ee))`;
    - marks the structural formula ready while keeping active value transport
      blocked on `R_Sigma(a)`, embedding frames/normals and connection variation;
    - Lean proves that the structural formula alone does not transport values
      without active embedding.
  - [x] Add formula-only embedding frame/normal trace transport:
    - records `e_a^mu = partial_a X^mu`,
      `h_ab = g_munu e_a^mu e_b^nu`, and normalized level-set normal;
    - keeps active trace transport blocked on regular embedding and nondegenerate
      induced metric;
    - Lean proves formulae alone do not close transport without embedding.
  - [x] Add `P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGate`:
    - aggregates `R_e`, `R_omega`, `R_psi`, `R_X`, and `R_matter`;
    - imports live tetrad, connection, spinor, embedding and matter-flux channel statuses;
    - keeps the residual one-form blocked until every channel coefficient is explicit.
  - [x] Add `P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGate`:
    - splits the residual one-form into tetrad/connection/spinor/embedding/matter channels;
    - imports the live residual-channel frontier instead of hard-coding component readiness;
    - blocks until those channel coefficients are explicit in the allowed basis.
  - [x] Add `P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGate`:
    - declares the field-space exactness test `d_field alpha_res = 0`;
    - blocks until the residual curl/cross-channel symmetry is proved.
  - [x] Add `P0EFTJanusZ2SigmaCountertermResidualExtractionGate`:
    - declares the residual one-form to primitive extraction problem;
    - imports live residual-one-form decomposition and integrability statuses;
    - blocks until `L_ct` is integrated from the explicit nonlinear residual.
  - [x] Add `P0EFTJanusZ2SigmaCountertermDensityExpansionGate`:
    - isolates the missing `L_ct(h,K,torsion,Immirzi)` expansion;
    - forbids new fitted counterterm freedom.
  - [x] Add `P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate`:
    - records the full residual-one-form -> primitive -> density -> radial-variation chain;
    - imports live residual-extraction, local-density-basis, density-expansion and radial-block statuses;
    - keeps `counterterm_block_reduced = false` until the chain closes.
  - [x] Add `P0EFTJanusZ2SigmaEmbeddingGaugePolicyGate`:
  - imports shell proper-time gauge as generic thin-shell machinery;
  - records radial/time embedding gauge choices as coordinate fixing only;
  - blocks using gauge choice as a substitute for deriving `R_Sigma(a)`.
- [x] Add `P0EFTJanusZ2SigmaEmbeddingGaugeEquationGate`:
  - imports induced-metric normalization for dynamic thin shells;
  - fixes `T_±` derivatives conditionally on `R_Sigma(a)`;
  - keeps `R_Sigma(a)` and therefore `X_±(a)` open.
- [x] Add `P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGate`:
  - records unknown embedding functions and declared constraints;
  - isolates missing `R_Sigma(a)` throat-radius law and embedding gauge;
  - prevents `X_±(a)` closure from being inferred by constraint naming alone.
- [x] Add `P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate`:
  - declares the active resolved-tunnel embedding problem `X_+^mu(a,xi)` and `X_-^mu(a,xi)`;
  - imports Janus projective/tunnel topology plus generic thin-shell embedding machinery;
  - blocks `DeltaK_s(a)` and `DeltaK_tau(a)` until the active embedding is derived.
- [x] Add `P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate`:
  - imports generic thin-shell embedding machinery;
  - declares `X_pm`, tangents, normals, induced metric matching and `K_ab^pm`;
  - derives `DeltaK_s` and `DeltaK_tau` structurally from `K_ab^pm`;
  - leaves active tunnel embedding functions of `a` open.
- [x] Add strict metric-geometry primitives:
  - builds inverse metric, Levi-Civita Christoffels, induced metric pullback and normalized level-set normal;
  - requires active metric, metric derivatives, level-set/embedding and explicit orientation/sign;
  - feeds the extrinsic-curvature tensor builder without Planck/LCDM/Z4 defaults.
- [x] Add strict extrinsic-curvature tensor builder:
  - computes `K_ab = -n_mu(partial_a partial_b X^mu + Gamma^mu_alpha_beta e_a^alpha e_b^beta)`;
  - reduces `K_s = gamma^{ij}K_ij/3` and `K_tau = K_tau_tau`;
  - requires active embedding derivatives, Christoffels, normals and spatial metric;
  - does not supply fitted geometry or Planck/LCDM/Z4 defaults.
  - [x] Add strict FLRW extrinsic-curvature grid builder:
    - evaluates active geometry data on `a_grid`;
    - outputs `K_s(a)` and `K_tau(a)` arrays for plus/minus sectors;
    - keeps values blocked until active embedding, connection and normals are supplied.
- [x] Add active embedding to FLRW extrinsic-curvature input adapter:
  - declares the contract
    `R_Sigma(a), X_±(a), tangents, normals, Christoffels -> flrw_extrinsic_curvature_grid_inputs.json`;
  - remains blocked until active tunnel embedding closure is derived;
  - prevents supplied K-array fixtures from being treated as Cartan-GHY source data.
- [x] Add `R_Sigma` solution to embedding/curvature branch bridge:
  - declares the single certificate route from solved throat radius to both
    Cartan-GHY embedding data and active dimensionful curvature/volume branch;
  - remains blocked until matter-flux and counterterm radial blocks are reduced.
- [x] Add strict FLRW extrinsic-curvature grid writer:
  - validates active plus/minus `K_s/K_tau(a)` arrays and explicit Z2 orientation;
  - writes `flrw_extrinsic_curvature_grid.json` only from active grid inputs;
  - feeds the Cartan-GHY DeltaK input writer without Planck/LCDM/Z4 defaults.
- [x] Add strict extrinsic-curvature jump builder:
  - computes `DeltaK_s = K_s_plus + eps_Z2 K_s_minus`;
  - computes `DeltaK_tau = K_tau_plus + eps_Z2 K_tau_minus`;
  - requires active plus/minus extrinsic curvatures and explicit Z2 orientation;
  - records that orientation is explicit and must not be fitted or silently changed;
  - keeps values blocked until active `K_ab^pm(a)` are derived from the tunnel embedding.
- [x] Add strict Cartan-GHY from extrinsic-curvature builder:
  - composes `K_s/K_tau ± -> DeltaK_s/tau -> rho_CGHY/p_CGHY`;
  - requires active plus/minus curvature functions and explicit `kappa*rho_crit0`;
  - introduces no new formula beyond the existing active projection convention.
- [x] Add strict critical-normalization builder:
  - builds `rho_crit0_Z2Sigma`, `kappa_Z2Sigma` and `kappa*rho_crit0`;
  - requires active `H0_Z2Sigma` and explicit gravitational constant convention;
  - forbids Planck/LCDM `H0` defaults and archived Z4 normalization.
- [x] Add strict background-scalar manifest writer:
  - validates `H0_Z2Sigma`, `omega_k_Z2Sigma`, `G_Z2Sigma` and critical-normalization provenance;
  - propagates scalar provenance into BAO component manifests;
  - requires `scalar_provenance` in active BAO component manifests before the active pipeline can consume them;
  - forbids compressed Planck/LCDM background, archived Z4 reuse and observational `H0` fitting.
- [x] Add `P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate`:
  - imports the generic Brown-York/Israel FLRW projection;
  - derives `rho_CGHY = 3 eps_Z2 DeltaK_s/kappa`;
  - derives `p_CGHY = eps_Z2(DeltaK_tau - 2 DeltaK_s)/kappa`;
  - leaves `DeltaK_s(a)` and `DeltaK_tau(a)` as active tunnel-embedding derivations.
- [x] Add `P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate`:
  - imports generic Holst/Nieh-Yan torsion literature;
  - blocks torsionless Holst from being used as a nonzero Sigma source;
  - leaves the active FLRW torsion pullback and dynamic-Immirzi boundary variation open.
- [x] Add `P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate`:
  - imports the standard shell flux one-form `T_munu e_a^mu n^nu`;
  - declares the transparency-condition option;
  - leaves active Janus throat flux or a transparency proof open.
- [x] Add `P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate`:
  - closes the standard trace-reversed FLRW junction algebra;
  - keeps `DeltaK_s(a)`, `DeltaK_tau(a)` and the non-circular source partition open.
- [x] Add `P0EFTJanusZ2SigmaCountertermFLRWObligationGate`:
  - records the unique Sigma counterterm and nonlinear residual cancellation;
  - leaves the active FLRW counterterm stress variation and `rho/p` reduction open.
- [x] Add `P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGate`:
  - declares the induced FLRW Sigma metric and Z2 normal orientation;
  - keeps all five component reductions open until derived on the active Sigma background;
  - blocks `T_eff_ab` projection to `rho_eff(a), p_eff(a)`.
- [x] Add `P0EFTJanusZ2SigmaProjectedStressTensorGate`:
  - defines the induced Sigma metric variation;
  - declares the Brown-York-like projected stress tensor;
  - applies the Z2 projection to the visible background.
- [x] Add `P0EFTJanusZ2SigmaTunnelJunctionConditionGate`:
  - declares the extrinsic-curvature jump across Sigma;
  - includes Z2 normal-orientation reversal;
  - derives the tunnel junction condition from projected Sigma stress.
- [x] Add `P0EFTJanusZ2SigmaEffectiveFluidClosureGate`:
  - primary thin-shell/Brown-York literature supplies the projection method;
  - no direct Janus `Z2_tunnel_Sigma` formula for `rho_eff(a), p_eff(a)` was imported;
  - structural projection is ready, numeric effective-fluid closure remains open.
- [x] Add `P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate`:
  - derives the structural effective Friedmann equation;
  - derives the structural acceleration equation;
  - derives the effective continuity equation;
  - no observational parameters are fitted.
- [x] Add active `P0EFTJanusZ2SigmaBackgroundEquationDerivationGate`:
  - Sigma boundary action is available;
  - projected Sigma stress tensor is derived;
  - Z2 tunnel junction condition is derived;
  - effective Friedmann/acceleration/continuity equations are derived;
  - legacy LCDM and archived Z4 backgrounds are forbidden.
- [x] Add `P0EFTJanusZ2SigmaNumericalBackgroundClosureGate`:
  - structural background equations are closed;
  - numerical `H_Z2Sigma(a)` remains blocked until `rho_eff(a)` and `p_eff(a)` are supplied from the active Sigma boundary action;
  - legacy LCDM and archived Z4 background callables remain forbidden.
- [x] Add `P0EFTJanusZ2SigmaDistanceBAOBibliographyGate`:
  - standard FLRW distance definitions are importable;
  - Etherington reciprocity is importable conditionally on null geodesics and photon conservation;
  - BAO sound-horizon machinery is importable generically;
  - Sigma photon map and Z2/Sigma `r_d` remain local derivations.
- [x] Split repository layout:
  - root `JanusFormal.lean` imports only `JanusFormal.ActiveZ2Sigma`;
  - active Z2/Sigma imports live in `JanusFormal/ActiveZ2Sigma.lean`;
  - historical modules stay in optional `JanusFormal/AllImportsArchive.lean`;
  - `docs/janus_repository_layout.md` indexes daily active vs archived commands.
- [x] Add `P0EFTJanusZ2SigmaPhotonGeodesicDistanceMapGate`:
  - visible photon metric projection declared;
  - photon null geodesic and redshift map derived;
  - `D_H`, `D_M`, `D_A`, `D_L` derived with Etherington guard.
- [x] Add `P0EFTJanusZ2SigmaBAOSoundRulerGate`:
  - photon-baryon sound speed declared;
  - drag epoch condition declared;
  - `r_d^Z2Sigma = integral c_s^Z2Sigma/H_Z2Sigma dz`;
  - fitted Planck `r_d` and compressed LCDM priors forbidden;
  - numerical evaluation remains blocked on active `H_Z2Sigma`, `c_s^Z2Sigma`, and `z_d^Z2Sigma`.
- [x] Add `P0EFTJanusZ2SigmaBAONonCompressedObservationGate`:
  - DESI DR2 Gaussian BAO mean vector and 13x13 covariance are ready;
  - compressed Planck `r_d` and archived Holst/Z4 BAO diagnostics are forbidden;
  - the gate remains red until active Z2/Sigma distances and `r_d` are computed.
- [x] Add `P0EFTJanusZ2SigmaBAOActiveReadinessGate`:
  - aggregates active `H_Z2Sigma`, `D_M/D_H/D_V`, `c_s`, `z_d`, `r_d` and DESI covariance readiness;
  - records that `src/janus_lab/z2_sigma_background.py` can assemble `rho_eff_Z2Sigma(a)` and `p_eff_Z2Sigma(a)` from active FLRW stress components;
  - records that `src/janus_lab/z2_sigma_background.py` has the strict `H_Z2Sigma(z)` callable builder and can construct values once active `H0_Z2Sigma`, `omega_k_Z2Sigma` and `rho_eff/rho_crit0(a)` are supplied;
  - records that `src/janus_lab/z2_sigma_early_plasma.py` can construct `c_s^Z2Sigma(z)` and solve `z_d^Z2Sigma` once active baryon/photon densities, `H_Z2Sigma` and drag rate are supplied;
  - records that `src/janus_lab/z2_sigma_bao.py` can compute DESI vectors and chi2 once active `H_Z2Sigma`, `omega_k_Z2Sigma` and `r_d` are supplied;
  - records that `src/janus_lab/z2_sigma_sound_ruler.py` can integrate `r_d^Z2Sigma` once active `H_Z2Sigma`, `c_s^Z2Sigma` and `z_d^Z2Sigma` are supplied;
  - keeps BAO chi2 blocked until those quantities are derived numerically;
  - forbids compressed Planck `r_d`, `planck_like_scale`, archived Z4 and phenomenological Holst BAO reuse.
- [x] Add a Z2/Sigma BAO chi2 dry-run:
  - proves the DESI vector/covariance pipeline computes when supplied explicit functions;
  - marks the result demo-only and forbids official use until active `H_Z2Sigma` and `r_d^Z2Sigma` replace demo inputs.
- [x] Add `P0EFTJanusZ2SigmaBAOOfficialChi2Gate`:
  - consumes only `outputs/active_z2_sigma/bao_inputs.json`;
  - requires manifest provenance `active_core = Z2_tunnel_Sigma` and `source = active_derived`;
  - rejects compressed Planck/LCDM `r_d`, archived Z4 reuse and phenomenological Holst BAO scans;
  - computes the DESI vector and covariance chi2 only when the active manifest exists.
- [x] Add strict scale-free BAO chi2 path:
  - can write `outputs/active_z2_sigma/bao_scale_free_inputs.json` from the active BAO component manifest;
  - consumes only active `E_Z2Sigma`, `c_s/c`, `Gamma_drag/H0`, `z_d` and `rhat_d = H0*r_d/c`;
  - requires scale-free provenance and `observational_H0_fit_used = false`;
  - verifies stored `rhat_d` against the dimensionless sound-ruler integral;
  - reports DESI prediction/residual vectors plus primitive audit samples;
  - remains non-official until active physical manifests exist.
- [x] Add active-inputs-to-scale-free-BAO-chi2 gate:
  - performs atomic preflight on background, FLRW and early-plasma active input manifests;
  - writes the component manifest, scale-free manifest and DESI scale-free chi2 in one controlled pass;
  - blocks before writing if counterterm `rho/p` is not derived from active Sigma radial reduction;
  - keeps the official dimensional BAO gate blocked and reports `Gamma_drag/H0` availability.
- [x] Add scale-free primitive-to-chi2 gate:
  - consumes the direct primitive manifest `bao_scale_free_primitive_inputs.json`;
  - solves `Gamma_drag/H0 = E` internally for `z_d`;
  - writes strict `bao_scale_free_inputs.json` and reuses the DESI scale-free chi2 gate;
  - rejects Planck/LCDM, archived Z4 and observational-H0 provenance.
- [x] Add split primitive assembler:
  - merges background dimensionless primitives with plasma/drag dimensionless primitives;
  - keeps the z grid and z_max aligned;
  - writes the canonical primitive manifest through the public strict writer.
- [x] Add scale-free primitive derivation frontier gate:
  - names the four remaining primitive derivations required for direct DESI BAO;
  - validates the split primitive manifests when present;
  - forbids compressed Planck/LCDM, archived Z4, observational-H0 and Holst-scan reuse.
- [x] Add component-to-split-primitive gate:
  - consumes the strict active BAO component manifest;
  - writes background and plasma scale-free primitive manifests;
  - keeps live BAO blocked until the component manifest itself exists.
- [x] Add component-to-primitive-chi2 gate:
  - composes the split primitive gate, canonical primitive assembler and
    primitive chi2 gate;
  - gives one command from active component manifest to DESI scale-free chi2;
  - still blocks live because no active component manifest exists.
- [x] Add active-inputs-to-primitive-chi2 gate:
  - composes strict active input writers, component manifest writer, primitive
    split/assembler path and DESI scale-free chi2;
  - keeps atomic preflight before writing intermediates and requires counterterm radial reduction.
- [x] Add `P0EFTJanusZ2SigmaBAOManifestSchemaGate`:
  - records the accepted manifest fields and provenance contract;
  - requires `input_provenance` for `H_Z2Sigma`, `c_s_Z2Sigma`, `z_d_Z2Sigma` and `r_d_Z2Sigma`;
  - requires `source_component_manifest_path` and `source_component_manifest_sha256` so official BAO inputs are traceable to the active component manifest;
  - exposes a strict writer/loader interface for future active derivations.
- [x] Add `P0EFTJanusZ2SigmaBAOActiveManifestPipelineGate`:
  - converts active FLRW component arrays plus early-plasma arrays into the official BAO input manifest;
  - remains blocked until `outputs/active_z2_sigma/bao_component_inputs.json` exists with active-derived provenance.
- [x] Add strict early-plasma component manifest writer:
  - validates `rho_baryon_Z2Sigma`, `rho_photon_Z2Sigma` and `Gamma_drag_Z2Sigma` arrays with active provenance;
  - can merge validated early-plasma payloads with independently derived FLRW components into a full BAO component manifest;
  - keeps `z_d` solving in the active BAO pipeline, where `H_Z2Sigma` is available;
  - rejects compressed Planck/LCDM, archived Z4 and Holst-scan provenance.
- [x] Add strict FLRW component manifest writer:
  - validates Cartan-GHY, Holst/Nieh-Yan, matter-flux and counterterm `rho/p` arrays on `a_grid`;
  - can merge background scalar, FLRW component and early-plasma manifests into the active BAO component manifest;
  - rejects compressed Planck/LCDM, archived Z4 and Holst-scan provenance.
- [x] Add `P0EFTJanusZ2SigmaBAOComponentManifestSchemaGate`:
  - declares the required component manifest fields;
  - includes explicit `critical_normalization` metadata with `kappa*rho_crit0_Z2Sigma`;
  - treats `z_d_bracket` as optional because the active pipeline can derive it from `Gamma_drag_Z2Sigma-H_Z2Sigma` on `z_grid`;
  - requires per-component provenance and rejects demo/LCDM/Planck/Z4/Holst-scan provenance tokens;
  - keeps `docs/templates/active_z2_sigma_bao_component_inputs.template.json` documentation-only, not an active output.
- [x] Add `P0EFTJanusZ2SigmaBAOComponentReadinessAuditGate`:
  - maps every active BAO component manifest field to its upstream gate;
  - separates dependent blockers such as `H0_Z2Sigma` and `kappa*rho_crit0_Z2Sigma` from direct FLRW stress-component blockers;
  - classifies `cartan_ghy_rho/p` as dependent on active `DeltaK_s/tau(a)` and critical normalization rather than as independent direct blockers;
  - classifies Holst/Nieh-Yan, matter-flux and counterterm `rho/p` fields as dependent on their active torsion, flux and counterterm reduction obligations rather than as standalone unknowns;
  - classifies `H0_Z2Sigma` as dependent on active time-gauge normalization, `rho_eff_Z2Sigma(a)` and tunnel embedding rather than as an observational fit input;
  - classifies `omega_k_Z2Sigma` as dependent on active projective curvature and tunnel embedding rather than an independent direct blocker;
  - classifies `rho_baryon_Z2Sigma` and `rho_photon_Z2Sigma` as dependent on active plasma normalizations rather than independent direct blockers;
  - classifies `Gamma_drag_Z2Sigma` as dependent on active photon/baryon plasma inputs instead of as an independent direct blocker;
  - emits a `root_obligations` list headed by `R_Sigma(a) -> X_±(a) -> DeltaK_s/tau(a)`, torsion pullback, Sigma transparency/counterterm and active early-plasma normalization;
  - reports the live radius/embedding frontier: conditional `R_Sigma(a) -> X_±(a)` is ready, but unconditional `R_Sigma(a)` and `X_±(a)` remain blocked by matter-flux, counterterm and `E_RSigma=0`;
  - keeps component-manifest writing blocked until active FLRW components, background scalars and early plasma are derived.
- [x] Add `P0EFTJanusZ2SigmaBAOComponentManifestWriterGate`:
  - writes `bao_component_inputs.json` from active component functions with strict provenance;
  - rejects forbidden demo/LCDM/Planck/Z4/Holst-scan provenance before the official BAO pipeline can consume it.
- [x] Add component-to-chi2 BAO dry-run:
  - exercises writer -> active manifest pipeline -> DESI chi2 calculator in a temporary directory;
  - marks the result dry-run only and not an official BAO evaluation.
- [x] Add strict Thomson drag-rate builder:
  - builds `Gamma_drag_Z2Sigma(z) = n_e,Z2Sigma sigma_T c / R_Z2Sigma`;
  - requires active free-electron, baryon and photon histories;
  - forbids Planck/LCDM recombination history defaults and archived Z4 inputs.
- [x] Add strict drag-epoch bracket finder:
  - locates active `Gamma_drag_Z2Sigma(z)-H_Z2Sigma(z)` sign changes on a supplied redshift grid;
  - forbids Planck/LCDM drag-epoch fits and archived Z4 inputs;
  - keeps `z_d^Z2Sigma` values blocked until active `H_Z2Sigma` and `Gamma_drag_Z2Sigma` are derived.
- [x] Add strict early-plasma density builders:
  - builds conserved active baryon and photon histories from active normalizations;
  - builds free-electron density from active baryon number and ionization histories;
  - forbids Planck/LCDM density parameters and recombination-history defaults.
- [x] Add strict early-plasma normalization builders:
  - builds baryon number density from active baryon mass density and explicit baryon-mass convention;
  - builds photon energy density from active blackbody temperature and explicit radiation constant;
  - keeps Planck `T_CMB`, `omega_b` and recombination histories forbidden as defaults.
- [x] Add strict Cartan-GHY component builder:
  - maps active `DeltaK_s(a)` and `DeltaK_tau(a)` to `rho_CGHY/rho_crit0` and `p_CGHY/rho_crit0`;
  - requires explicit Z2 orientation and `kappa*rho_crit0`;
  - does not infer Planck/LCDM normalization or reuse archived Z4 inputs.
- [x] Add strict Cartan-GHY component writer from `DeltaK` inputs:
  - consumes `cartan_ghy_deltaK_inputs.json` plus active `background_scalars.json`;
  - writes `cartan_ghy_components.json` only with active `DeltaK_s/tau(a)` and `kappa*rho_crit0`;
  - remains blocked until active tunnel embedding and active background normalization exist.
- [x] Add strict Cartan-GHY DeltaK input writer:
  - consumes active `flrw_extrinsic_curvature_grid.json`;
  - computes `DeltaK_s/tau = K_plus + eps_Z2 K_minus` with explicit orientation;
  - writes `cartan_ghy_deltaK_inputs.json` only from active plus/minus extrinsic-curvature arrays.
- [x] Add strict Holst/Nieh-Yan component writer:
  - consumes active `holst_nieh_yan_component_inputs.json`;
  - writes `holst_nieh_yan_components.json` only after active FLRW Holst/Nieh-Yan reduction;
  - rejects Planck/LCDM/Z4/Holst-scan provenance.
- [x] Add strict counterterm component writer:
  - consumes active `counterterm_component_inputs.json`;
  - writes `counterterm_components.json` only after active FLRW counterterm and radial reduction;
  - rejects Planck/LCDM/Z4/Holst-scan provenance.
- [x] Add strict non-matter FLRW inputs assembler:
  - merges Cartan-GHY, Holst/Nieh-Yan and counterterm component payloads;
  - writes `flrw_component_inputs_without_matter_flux.json` only when all three exist with aligned active grids.
- [x] Add strict matter-flux component builder:
  - permits zero matter-flux components only after active Sigma transparency is derived;
  - forbids silently setting `matter_flux_rho/p = 0` without a transparency proof.
- [x] Add `P0EFTJanusZ2SigmaGrowthBibliographyGate`:
  - standard scalar perturbation framework is importable;
  - bimetric and Einstein-Cartan perturbation contexts exist;
  - complete Z2/Sigma growth equations remain a local derivation.
- [x] Add `P0EFTJanusZ2SigmaGrowthPerturbationEquationGate`:
  - continuity and Euler perturbation rows derived;
  - Poisson/slip/friction family derived for the active Z2/Sigma core.
- [x] Add `P0EFTJanusZ2SigmaGrowthNonCompressedObservationGate`:
  - SDSS/eBOSS DR16 direct `f_sigma8` points and 5x5 covariance are ready;
  - archived Holst/Z4 growth curves and compressed Planck priors are forbidden;
  - the gate remains red until an active Z2/Sigma prediction vector is computed.
- [x] Add `P0EFTJanusZ2SigmaGrowthPredictionVectorGate`:
  - prevents reusing the archived Holst/Z4 growth solvers as active Z2/Sigma evidence;
  - blocks until numerical `H`, `Omega_m`, `mu`, slip and friction closures are supplied;
  - requires an explicit initial-condition and `sigma8` normalization policy.
- [x] Add `P0EFTJanusZ2SigmaCMBNonCompressedObservationGate`:
  - local non-compressed Planck low-l, lowE, high-l TTTEEE and lensing likelihood paths are available;
  - archived Z4 CMB spectra and compressed Planck LCDM priors are forbidden;
  - the gate remains red until active Z2/Sigma TT/TE/EE/PP spectra are generated and handshaken.
  - Z2/Sigma Poisson constraint, slip relation and friction term derived;
  - archived Z4 `mu` reuse forbidden.
- [x] Add `P0EFTJanusZ2SigmaCMBBoltzmannBibliographyGate`:
  - Ma/Bertschinger and CLASS/CAMB equation machinery are importable;
  - complete Z2/Sigma CMB Boltzmann equations remain local.
- [x] Add `P0EFTJanusZ2SigmaCMBBoltzmannEquationGate`:
  - photon temperature and polarization hierarchies declared;
  - baryon and neutrino couplings declared;
  - Z2/Sigma metric source terms derived;
  - archived Z4 CMB reuse forbidden.
- [x] Add `P0EFTJanusZ2SigmaNonCompressedObservationGate`:
  - all equation locks are closed;
  - direct growth, BAO and CMB gates remain to run;
  - compressed LCDM validation remains forbidden;
  - full no-fit cosmology remains false.
- [x] Add active facade audit:
  - `JanusFormal.lean` imports only Z2/Sigma active gates;
  - old CMB/Z4 modules stay in `JanusFormal.AllImportsArchive`.
- [x] Add docs alignment audit to prevent active-Z4 wording from returning.
- [x] Archive legacy `Z4` as diagnostic-only with
  `P0EFTJanusLegacyZ4ArchivePolicyGate`.
- [x] Add Z2/Sigma replacement gates:
  - `P0EFTJanusRP4PinSignComputationGate`;
  - `P0EFTJanusRP4PinSignAuditGate`;
  - `P0EFTJanusProjectiveTunnelCoverRatioGate`;
  - `P0EFTJanusSigmaBoundaryActionSupportGate`.
- [x] Add `P0EFTJanusSigmaBoundaryVariationalDecompositionGate`:
  - induced Sigma measure;
  - Cartan/GHY, Holst/Nieh-Yan, matter-flux and tunnel-junction terms;
  - tetrad, connection and spinor variation channels;
  - nonlinear residual obstruction isolated.
- [x] Compute `RP4` base Pin sign:
  - `w(T RP4) = (1 + a)^5 = 1 + a + a^4` mod 2;
  - `w1 != 0`, `w2 = 0`, `w1^2 != 0`;
  - `Pin+` exists on the `RP4` base;
  - `Pin-` is obstructed on the `RP4` base.
- [x] Add `P0EFTJanusSigmaAPSPinLiftObligationGate`:
  - induced Pin structure on `Sigma`;
  - APS boundary projector;
  - Fredholm domain;
  - eta/zero-mode cancellation;
  - parity anomaly cancellation.
- [x] Add `P0EFTJanusSigmaAPSLocalThroatModelGate`:
  - compact orientable Sigma throat local model;
  - local induced Pin/spin data;
  - local APS projector and Fredholm domain;
  - eta/parity handled by subsequent gates.
- [x] Add `P0EFTJanusSigmaAPSEtaCancellationGate`:
  - Sigma Dirac spectrum paired;
  - Sigma Dirac kernel trivial;
  - `eta=0`, `h=0`, and APS correction contribution zero;
  - parity handled by subsequent parity gate.
- [x] Add `P0EFTJanusSigmaAPSParityAnomalyCancellationGate`:
  - Z2 tunnel pairing declared;
  - paired boundary orientation reversal declared;
  - opposite Dirac determinant phases declared;
  - parity anomaly cancels pairwise;
  - Sigma APS boundary Pin lift closed.
- [x] Add `P0EFTJanusSigmaAPSTraceRegularizationGate`:
  - Clifford trace normalization declared;
  - APS heat-kernel regularization declared;
  - trace regularization standard globally.
- [x] Add `P0EFTJanusZ4PureMathClosureAuditGate`.
- [x] Add `P0EFTJanusZ4HardGlobalTheoremAvailabilityGate`.
- [x] Add `P0EFTJanusZ4HardGlobalTheoremReductionGate`.
- [x] Add hard external theorem target registry.
- [x] Reduce APS/Pin index package to atomic global obligations.
- [x] Reduce orbifold 2:1 theorem to atomic global cover-ratio obligations.
- [x] Add `P0EFTJanusZ4FullActionAtomicClosureGate`.
- [x] Close determinant-measure insertion bridge into full action assembly.
- [x] Add boundary pure-closure obstruction gate.
- [x] Derive the identity-channel EFT counterterm from the Janus volume-solder
  invariant at the algebraic boundary-identity level.
- [x] Reduce nonlinear boundary variation to atomic tetrad/connection/membrane
  obligations.
- [x] Reduce Ward closure to atomic weighted-current, divergence, anomaly, and
  obstruction obligations.
- [x] Reduce nonlinear Euler-Lagrange residuals to one common obstruction `O_nl`.
- [x] Reduce gauge-fixing variation uniqueness to an atomic obligation.
- [x] Close the nonlinear boundary variation so the full boundary action is
  closed beyond the algebraic identity-channel counterterm bridge.
- [ ] Prove residual gauge freedom is removed by Janus geometry.
- [ ] Prove the common nonlinear Euler-Lagrange obstruction `O_nl = 0`.
- [ ] Close the Ward/global anomaly branch without axioms.
- [x] Prove `Sigma` APS boundary Pin lift without axioms.
- [x] Prove projective-tunnel cover/quotient volume ratio and uniqueness.
- [x] Close active Janus Z2/Sigma/Holst Sigma boundary action without axioms.
  Sigma support, variational package, nonlinear residual cancellation, and full
  boundary action are closed for the active pure-math ledger.
- [ ] Only after non-compressed Planck + BAO + growth pass under one derived
  observational model: consider `full_cosmology_prediction_ready_no_fit = true`.

### Active objective: hard global theorems (APS/Pin + orbifold 2:1 + unique action)

- Canonical execution plan moved to: [active_objective_hard_global_lock.md](docs/active_objective_hard_global_lock.md)

- [x] Establish `aps_index_package_closed` as a non-axiomatic theorem in Lean from
  concrete local-global data:
  - local Sigma APS projector/Fredholm package is closed;
  - Sigma eta/zero-mode package is closed;
  - Sigma global parity anomaly cancellation is closed;
  - trace regularization standard is closed.
- [x] Establish projective-tunnel cover-ratio lock:
  - `global_projective_tunnel_volume_ratio_two_to_one`
  - `global_volume_ratio_unique_two_to_one`
- [x] Close the combined Z2/Sigma action-to-equations interface for the active
  pure-math boundary/action ledger (without
  introducing new phenomenological assumptions):
  - single tunnel-supported source on `Sigma`
  - Sigma-supported variational decomposition
  - nonlinear residual cancellation
  - full boundary action closure
- [x] Update the hard-global/observational readouts so lock status is:
  - APS lock closed,
  - projective tunnel 2:1 lock closed,
  - Sigma boundary action lock closed,
  - no promotion of `planck` verdict and no `full_cosmology_prediction_ready_no_fit`.
- [x] Freeze CMB/observational gates separately from the active pure-math closure.

## Archived CMB/Z4 master-equation lock

- [x] Archive patchwork slip/surface/minus-sector attempts as diagnostic-only
  when their observable response remains carrier-tangent.
- [x] Archive the unique Z4 master-equation path and require all observable
  deltas to descend from one upstream `U_Z4` generator.
- [x] Find a non-tangent localized-transition master ansatz:
  source-level replay parallel fraction is about `0.1906`.
- [x] Generate internal diagnostic spectra only; official Planck likelihood
  remains forbidden.
- [x] Lock the raw master spectra before likelihood because TT/EE zero-count
  artifacts and large fractional deviations are present.
- [x] Add bounded-tanh shape regularization as a diagnostic:
  it clears the pre-likelihood shape artifacts and keeps carrier projection
  below threshold, but it is not action-derived.
- [x] Derive the bounded response as membrane transport:
  `dR/dS = 1 - (R/L)^2`, `R = L*tanh(S/L)`.
- [x] Regenerate diagnostic spectra from the membrane-transport regularized
  master source.
- [x] Add the regularized diagnostic shape report gate before any likelihood
  handshake.
- [x] Derive the membrane transport normalization from the upstream Z4
  membrane/orbifold lock: `L_transport = a_sigma = 2/3`.
- [x] Add `MasterActionNormalizationGate` to block likelihood handshakes until
  that normalization is derived from the Z4 action, membrane junction terms, or
  orbifold boundary conditions.
- [x] Add `MasterLikelihoodHandshakeGate`; no official Planck trial before this
  handshake passes.
- [x] Add `MasterDiagnosticLikelihoodTrialGate`; still no candidate promotion
  without an explicit diagnostic result.
- [x] Add official likelihood policy gate separating internal pseudo-likelihood
  from any observed Planck run.
- [x] Add observed Planck wrapper handshake gate only after wrapper, nuisance,
  non-overlap, GR reference, and no-retuning replay policies are explicit.
- [x] Detect complete observed Planck wrapper coverage for high-l, low-l, and
  lensing components.
- [x] Provide a GR reference handshake report on the same observed Planck
  wrapper before any master no-retuning replay.
- [x] Re-run `MasterObservedPlanckWrapperHandshakeGate` after the GR report.
- [x] Add `MasterNoRetuningReplayGate`; master source hash and
  `L_transport = a_sigma = 2/3` remain frozen.
- [x] Add observed Planck diagnostic trial gate. No promotion without a clean
  non-overlap result.
- [ ] Execute observed diagnostic trial explicitly if needed, then add
  `MasterObservedNonOverlapAccountingGate`.
- [x] Execute observed diagnostic trial once locally:
  combined non-overlap is strongly positive, so the observed master branch is
  rejected as currently normalized.
- [x] Add `MasterObservedNonOverlapAccountingGate`; it records rejection and
  never promotes directly.
- [x] Add `MasterObservedFailureMapGate` to localize the high-l failure.
- [x] Scan upstream master high-l acoustic shape revisions:
  channel-wise `_unit` normalization is replaced by shared `U_Z4`
  normalization plus a Silk/high-l guard.
- [x] Regenerate source-level master v2 from the selected upstream revision
  before any new observed rerun.
- [x] Run carrier-tangent projection on the revised source-level master v2.
- [x] Regenerate v2 diagnostic spectra from the revised master source.
- [x] Audit v2 diagnostic spectra shape/non-overlap before any likelihood gate.
- [x] Add/clear the v2 pre-likelihood lock before any observed likelihood gate.
- [x] Derive/check v2 action normalization before any likelihood handshake.
- [x] Only after v2 action normalization: run the next likelihood handshake
  gate. No Planck claim before that.
- [x] Open only a diagnostic v2 likelihood trial gate; no official Planck
  claim or candidate promotion.
- [x] Add v2 official-likelihood policy gate before any observed wrapper use.
- [x] Add v2 observed-wrapper/GR-reference handshake before any observed trial.
- [x] Add v2 no-retuning replay before any observed Planck trial.
- [x] If proceeding beyond the stop line, open only an observed diagnostic trial
  gate; no promotion or full validation.
- [x] If an observed run is explicitly requested, route result through v2
  non-overlap accounting before any interpretation.
- [ ] Keep official Planck validation false unless a later explicit observed
  run passes non-overlap and additional stability gates.
- [x] Add complete-solver observed Planck diagnostic/export gate and complete
  non-overlap accounting gate. These are diagnostic-only and keep validation
  and promotion false.
- [x] Execute the complete-solver observed diagnostic once:
  available high-l+lensing combined delta is positive, available decomposed
  delta is positive, low-l is non-finite, and the branch is rejected.
- [x] Add the complete-solver Z4-off GR-limit shape gate. Z4-on Planck
  interpretation is blocked unless the native GR limit matches CAMB-GR shape.
- [x] Anchor the Z4-off GR limit to the regenerative CAMB-GR provider instead
  of the internal LOS proxy.
- [x] Add `SolverInputManifestGate`; current Z4-on Planck interpretation is
  blocked by hidden/default Z4 inputs, unspecified minus-sector microphysics,
  hardcoded initial mode, and LS channel calibration.
- [ ] Replace LS channel calibration with unit-only conversion or a declared
  physical amplitude.
- [ ] Declare Z4 initial mode, boundary conditions, projection map, and
  minus-sector microphysics before the next observed Z4-on interpretation.

## Priority 1 - Define the bi-sector model

- [x] Write the first minimal linear Janus-orbifold prototype with two sectors:
  - visible/positive sector;
  - mirror/negative sector;
  - coupling matrix between density, velocity and potentials;
  - membrane/orbifold junction at `a_sigma = 2/3`;
  - observable photon projection.
- [x] State and test the GR/LambdaCDM limit when Janus couplings go to zero.
- [ ] State which metric controls:
  - background expansion `H(a)`;
  - photon-baryon acoustic perturbations;
  - lensing Weyl potential;
  - BAO ruler `r_d`.

## Priority 2 - Build a minimal Janus-Boltzmann prototype

- [x] Create a small Python prototype, separate from CAMB:
  - background ODE;
  - two-sector scalar perturbations;
  - photon observable projection;
  - no recombination complexity at first.
- [x] Verify first numerical sanity gates:
  - recovers LambdaCDM in the zero-coupling limit;
  - conserves total constraint equations;
  - stable through the membrane crossing.
- [x] Compare only proxy observables first:
  - `theta_*`;
  - `r_d`;
  - Weyl/lensing proxy;
  - TT peak-shift proxy.

## Priority 3 - Decide backend strategy

- [ ] If the prototype reduces to effective single-sector source functions, keep CAMB/CLASS hooks.
- [ ] If it needs two dynamical metric sectors, stop treating CAMB as final validation.
- [ ] Evaluate CLASS/hi_class as the next backend before any from-scratch full solver.
- [ ] Keep CAMB fork as a diagnostic baseline only.

## Priority 4 - Observational gates

- [x] Add native GR vs CAMB reference gate.
- [x] Add native GR decomposition gate:
  - interface sanity;
  - acoustic background geometry;
  - visibility;
  - fixed-k source diagnostics;
  - unlensed TT/TE/EE bands;
  - lensing/phiphi split marker.
- [ ] Fix native GR baseline before any new Z4 physics:
  - high-TT chi2/dof against CAMB is too high;
  - TE phase/shape is wrong;
  - EE and lensing shapes are wrong;
  - first TT peak is shifted by more than the allowed tolerance.
- [x] Test whether projection/acoustic warping alone can repair native GR:
  - result: insufficient;
  - source/LOS engine repair is required before Z4.
- [x] Add GR backend policy:
  - CAMB is the strict GR reference backend while native GR is broken;
  - native Planck interpretation remains blocked;
  - Z4 corrections remain blocked unless implemented as controlled deviations
    around a verified GR baseline.
- [x] Export CAMB GR baseline in the native spectra schema:
  - this provides a safe GR/Z4-off baseline;
  - dominant TT/TE mismatch is reduced on the baseline path;
  - the toy native source engine remains explicitly unrepaired.
- [x] Route default Cobaya provider to the safe CAMB-GR baseline:
  - toy native LOS spectra are now explicit diagnostics only;
  - Planck default path no longer uses the broken toy baseline.
- [x] Add controlled Z4 deviation gate:
  - `lambda_Z4 = 0` reproduces CAMB-GR roundtrip;
  - raw native toy LOS spectra are forbidden for Planck;
  - all deltas must be tagged by physical channel;
  - spectrum-level deltas are debug-only unless source/transfer coherence is proven.
- [x] Add first nonzero internal delta gate: Weyl/lensing kernel:
  - unlensed TT/TE/EE unchanged;
  - `C_L^phiphi` convention checked;
  - small-lambda response finite and continuous;
  - nonzero Z4 remains not Planck-eligible until remapping/eligibility gates exist.
- [x] Add lensed remapping response gate:
  - CAMB-GR unlensed input plus Z4 `phiphi` delta;
  - unlensed primary remains unchanged;
  - lensed TT/TE/EE response is finite and continuous;
  - acoustic peak/TE-zero jumps are blocked;
  - current response is screened as a uniform phiphi-amplitude delta;
  - observable lensing requires a shape delta or more physical remapping kernel;
  - nonzero Z4 still needs a separate Planck eligibility gate.
- [x] Add lensing shape-delta gate:
  - classify the first Weyl/lensing delta as near-uniform amplitude response;
  - add a non-constant kernel/source-level `C_L^phiphi` shape response;
  - verify lambda-zero identity and small-lambda remapping continuity;
  - keep nonzero Z4 Planck-forbidden until an eligibility gate exists.
- [x] Add nonzero-Z4 Planck eligibility gate:
  - authorizes only `CAMB-GR + Weyl/lensing shape delta` likelihood trials;
  - does not claim Planck success;
  - keeps native toy LOS forbidden;
  - requires lambda-zero identity, channel isolation and small-lambda stability.
- [x] Add first signed Planck trial scaffold:
  - exports `CAMB-GR + Weyl/lensing shape delta` spectra for small signed lambdas;
  - uses only the eligible shape channel;
  - records band responses and optional official likelihood rows;
  - keeps trial execution separate from Planck success.
- [x] Add lensing component projection gate:
  - separates amplitude-only, shape-only and full `C_L^phiphi` deltas;
  - measures available Planck response per component;
  - demotes lensing-only if all component responses remain negligible.
  - result: best available `delta_chi2` is still negligible
    (`amplitude_only ~ -0.0346`, `shape_only ~ -0.0266`, `full ~ -0.0080`);
    lensing-only is diagnostic/calibration, not a Planck rescue channel.
- [x] Add late-ISW source delta gate:
  - source-level only, no direct `C_l` patch;
  - late ISW enabled, early ISW disabled;
  - recombination, visibility, acoustic phase, polarization and primordial
    spectrum deltas remain frozen;
  - Planck trial remains blocked until Weyl+late-ISW consistency is derived.
- [x] Add Weyl+late-ISW consistency gate:
  - one shared `X_Z4(k,tau)=delta(Phi+Psi)`;
  - lensing kernel uses `X_Z4`;
  - late ISW source uses `dX_Z4/dtau` with a late-time window;
  - independent lensing/ISW Weyl patches are forbidden;
  - recombination, visibility, acoustic phase and polarization remain unchanged;
  - controlled Weyl+late-ISW Planck trial is allowed only after this gate.
- [x] Add official Weyl+late-ISW trial scaffold:
  - uses shared Weyl/lensing plus late-ISW source;
  - early ISW, acoustic, recombination and polarization deltas are disabled;
  - exports signed lambda spectra and optional Planck likelihood rows;
  - remains an effective trial, not a full native-Z4 verdict.
- [x] Close Weyl+late-ISW as diagnostic only:
  - best available response is `delta_chi2 ~= -0.0037` at `lambda_Z4=-0.01`;
  - the channel is coherent but observationally negligible;
  - do not rescue Planck by increasing lambda outside the controlled small-delta regime.
- [x] Add metric-potential split gate:
  - preserve `X_Z4 = delta(Phi+Psi)`;
  - define explicit `deltaSlip_Z4 = delta(Phi-Psi)`;
  - reconstruct `deltaPhi` and `deltaPsi` without independent hidden sources;
  - keep eta and mu/Sigma as guarded diagnostics, not primary variables;
  - keep acoustic, recombination, visibility, polarization and primordial deltas disabled.
- [x] Add acoustic-driving delta gate after metric split:
  - use explicit `deltaPhi` and `deltaPsi`;
  - allow only early-ISW/acoustic gravitational driving;
  - keep recombination, visibility, `r_s`, `r_d`, background projection and primordial spectrum frozen;
  - report TT peak shifts, TE zero crossings, EE peak shifts and early-ISW response.
- [x] Add official acoustic-driving Planck trial:
  - backend remains `CAMB-GR + Z4 delta`;
  - enabled channel is `acoustic_temperature_source`;
  - split trials into `surface_only`, `early_isw_only` and `full`;
  - TE may respond through temperature only;
  - EE, visibility, recombination, primordial spectrum and lensing remain frozen;
  - report as controlled trial, not a full native-Z4 verdict.
- [ ] Interpret acoustic-driving trial result:
  - current best controlled response is `early_isw_only` at `lambda_Z4=-0.01`;
  - `delta_chi2_total_available ~= -7.605`;
  - `surface_only` is negligible (`~=-3.8e-5`);
  - no surface/eISW cancellation detected;
  - high-l TT and high-l TTTEEE both improve on available channels;
  - EE remains frozen by construction;
  - next likely gate: `PolarizationSourceDeltaGate` or a tighter TE phase diagnostic;
  - if high-l explodes, audit acoustic window and Bessel projection convention.
- [x] Add acoustic phase consistency gate:
  - refined `early_isw_only` lambda scan around `-0.01`;
  - TT peak and TE zero-crossing diagnostics;
  - channel-level Planck chi2 breakdown;
  - EE and `C_phi_phi` frozen guards;
  - blocks polarization if the best point is a scan-edge artifact.
- [x] Run acoustic phase consistency gate:
  - best refined `lambda_Z4 = -0.008`;
  - `delta_chi2_total_available ~= -8.414`;
  - best point is not a scan-edge artifact;
  - TE phase guard passed;
  - EE and `C_phi_phi` are frozen by construction;
  - Planck lensing likelihood moves by `~=-0.98` despite frozen `C_phi_phi`, so keep a subdominant-adapter warning.
- [ ] Open `PolarizationSourceDeltaGate` only with lensing-adapter warning preserved:
  - keep recombination and visibility frozen;
  - open only the quadrupole / `Pi` source response;
  - do not reinterpret the acoustic phase gate as a full Planck success.
- [x] Add Planck lensing input-dependence gate:
  - compare A: `C_phi_phi=GR`, CMB=GR;
  - B: `C_phi_phi=GR`, CMB acoustic delta;
  - C: `C_phi_phi` control, CMB=GR;
  - D: `C_phi_phi` control, CMB acoustic delta;
  - classify lensing likelihood motion as primary-CMB input dependence, not Z4 lensing.
- [x] Run Planck lensing input-dependence gate:
  - B-A primary CMB dependence: `~=-0.980`;
  - C-A phiphi control: `0`;
  - D-A combined: `~=-0.980`;
  - classify the lensing likelihood motion as primary-CMB input dependence.
- [x] Add polarization source delta gate:
  - source-level E transfer only;
  - subchannels: `E_source_projection_only`, `Theta2_quadrupole_response`, `Pi_source_response`, `full_polarization_source`;
  - keep recombination, visibility, background, `r_s/r_d`, primordial, lensing and slip frozen;
  - do not allow a Planck polarization trial until a separate trial scaffold is added.
- [x] Add controlled polarization-source Planck trial:
  - keep temperature channel fixed at `lambda_ref=-0.008`;
  - scan polarization subchannels separately;
  - preserve the lensing input-dependence classification.
- [ ] Interpret controlled polarization-source Planck trial:
  - current best subchannel is `Theta2_quadrupole_response`;
  - best `lambda_E=-0.02`, at scan edge;
  - incremental polarization gain over temperature-only: `~=-1.079`;
  - all subchannels prefer the negative scan edge;
  - keep standalone TE/EE caveat visible;
  - do not open joint acoustic-polarization consistency until lambda_E normalization is derived or the scan finds a non-edge optimum.
- [x] Add and run polarization edge phase audit:
  - extended negative `lambda_E` scan;
  - best subchannel remains `Theta2_quadrupole_response`;
  - best `lambda_E=-0.02` is now bracketed, not scan-edge;
  - incremental gain remains `~=-1.079`;
  - best-point TE/EE phase guard passes;
  - TT and `C_phi_phi` are invariant under `lambda_E`;
  - full extended scan perturbativity fails at large `|lambda_E|`, so only the bracketed best region is interpretable.
- [x] Add and run acoustic-polarization joint consistency gate:
  - best point: `lambda_T=-0.008`, `lambda_E=-0.02`;
  - joint delta chi2: `~=-9.492`;
  - temperature-only contribution: `~=-8.414`;
  - polarization-only contribution: `~=-0.912`;
  - interaction term: `~=-0.166`, small relative to the joint response;
  - hard TE phase guard passes, but TE/EE residual smoothness guards fail;
  - `C_phi_phi`, visibility, background, `r_s/r_d` and primordial sectors remain frozen;
  - verdict: useful coherent-source diagnostic, not promotable to full Planck/native-Z4.
- [ ] Derive the real `Theta2` tight-coupling closure and TE/EE transport smoothness:
  - do not continue by widening likelihood scans;
  - replace effective `Theta2_quadrupole_response` with an action-derived closure.
- [x] Add and run `Theta2TightCouplingClosureGate`:
  - previous status: `source_tagged_effective`;
  - new status: `tight_coupling_derived_effective`;
  - `Theta2` depends on `k/kappadot`, velocity/dipole proxy and metric driving;
  - response vanishes in the strong tight-coupling limit;
  - response remains regular at the visibility peak;
  - response is smooth in `k` and `tau`;
  - full Boltzmann hierarchy remains open.
- [x] Add and run `TEEETransportSmoothnessGate`:
  - compares old `source_tagged_effective` transport to the new tight-coupling transport;
  - TE second-difference ratio new/old: `~=0.900`;
  - EE second-difference ratio new/old: `~=0.267`;
  - direct `C_l`, native toy LOS, recombination, visibility, background, `r_s/r_d`, primordial, lensing and slip remain frozen.
- [ ] Rerun acoustic-polarization joint consistency with `tight_coupling_derived_effective` `Theta2`:
  - compare old joint result `delta_chi2 ~= -9.492` to new closed-transport result;
  - require interaction term to remain small;
  - require TE/EE smoothness to remain improved;
  - still not a full Planck verdict.
- [x] Add and run closed-Theta2 acoustic-polarization joint gate:
  - best point remains `lambda_T=-0.008`, `lambda_E=-0.02`;
  - new joint delta chi2: `~=-9.199`;
  - old tagged-source joint delta chi2: `~=-9.492`;
  - new interaction term: `~=-0.155`;
  - hard phase, TE smoothness and EE smoothness guards pass;
  - promote only to `effective_acoustic_polarization_candidate`;
  - full Planck verdict remains false.
- [ ] Open Boltzmann hierarchy closure roadmap:
  - promote `tight_coupling_derived_effective` only after deriving photon multipoles, polarization multipoles, collision terms and free-streaming transition.
- [x] Add and run photon/polarization Boltzmann hierarchy closure gate:
  - scalar mode only;
  - `B` modes disabled or GR-only;
  - `Theta_l` and `E_l` multipoles declared up to `lmax=24`;
  - `Pi` source derived from multipoles;
  - no free `Theta2` source tag;
  - TCA, transition and free-streaming regimes declared;
  - TCA switch smoothness passes;
  - strong TCA suppression passes;
  - `lmax` convergence passes;
  - status: `boltzmann_hierarchy_closed_effective`;
  - full Planck verdict remains false.
- [ ] Run `official_planck_closed_boltzmann_acoustic_polarization_trial`:
  - start at `lambda_T=-0.008`, `lambda_E=-0.02`;
  - use small local scan only;
  - compare against closed-Theta2 effective gain `~=-9.199`;
  - do not label as full Z4 Planck verdict.
- [x] Run `official_planck_closed_boltzmann_acoustic_polarization_trial`:
  - best point remains `lambda_T=-0.008`, `lambda_E=-0.02`;
  - closed-Boltzmann gain: `~=-9.201`;
  - closed-Theta2 reference gain: `~=-9.199`;
  - gain preservation ratio: `~=1.000`;
  - interaction term: `~=-0.155`;
  - TE/EE smoothness, TCA switch, strong TCA suppression and `lmax` convergence pass;
  - standalone high-l TE/EE remains unavailable locally;
  - promote only to `boltzmann_closed_effective_z4_cmb_candidate`;
  - full Planck verdict remains false.
- [x] Add and run Planck likelihood completeness gate:
  - available: low-l TT, low-l EE, lensing, high-l TT, high-l TTTEEE;
  - missing locally: standalone high-l TE and standalone high-l EE;
  - candidate trial allowed: true;
  - full Planck validation allowed: false;
  - generated outputs not imported as theory sources.
- [x] Add and run closed-Boltzmann candidate robustness gate:
  - best point stable: true;
  - local curvature detected: true;
  - best lambda not edge: true;
  - gain remains below `-5`;
  - lmax/TCA robustness passes;
  - TE/EE smoothness remains pass;
  - full Planck verdict remains false.
- [x] Freeze closed-Boltzmann candidate spec:
  - candidate: `P0EFTJanusZ4ClosedBoltzmannAcousticPolarizationCandidate`;
  - backend: `camb_gr_plus_z4_delta`;
  - `lambda_T=-0.008`, `lambda_E=-0.02`;
  - recombination, visibility, background projection, `r_s/r_d`, primordial spectrum, `C_phi_phi`, slip, mirror sector and raw native toy LOS remain frozen.
- [x] Add standalone TE/EE acquisition gate:
  - robust available-channel candidate: true;
  - standalone high-l TE available: false;
  - standalone high-l EE available: false;
  - no parameter retuning or new physics allowed before acquisition;
  - full high-l decomposition trial remains blocked.
- [x] Acquire or connect standalone high-l TE/EE likelihoods:
  - local Cobaya wrappers exist: `planck_2018_highl_plik.TE`, `planck_2018_highl_plik.EE`;
  - required standalone data are installed locally: `plik_rd12_HM_v22_TE.clik`, `plik_rd12_HM_v22_EE.clik`;
  - rerun the same frozen candidate only;
  - output high-l TT, TE, EE, TTTEEE, low-l TT/EE and lensing deltas separately.
- [x] Run standalone high-l TE/EE GR reference handshake:
  - check `C_l/D_l`, units, TE sign, `ell` indexing, nuisance vector, foreground handling, GR reference sanity;
  - GR/CAMB reference passed for standalone TE/EE;
  - frozen candidate high-l decomposition trial is now allowed.
- [x] Run frozen candidate high-l decomposition trial:
  - no retuning: `lambda_T=-0.008`, `lambda_E=-0.02`;
  - `delta_chi2_highl_TT = -3.5043`;
  - `delta_chi2_highl_TE = +0.0412`;
  - `delta_chi2_highl_EE = -0.2733`;
  - `delta_chi2_highl_TTTEEE = -4.1114`;
  - `delta_chi2_lensing = -1.5779`;
  - `delta_chi2_total = -9.4326`;
  - full Planck validation remains false.
- [x] Add non-overlapping likelihood accounting:
  - legacy overlapping total `-9.4326` is diagnostic only;
  - combined high-l basis total: `-5.6962`;
  - decomposed high-l basis total: `-5.3212`;
  - do not add `highl_TTTEEE` together with standalone `highl_TT/TE/EE`.
- [x] Promote frozen candidate as high-l decomposed effective candidate:
  - `planck_highl_decomposed_effective_candidate = true`;
  - standalone TE cost is small: `+0.0412`;
  - standalone EE improves: `-0.2733`;
  - full Planck validation remains false.
- [x] Add candidate nuisance/foreground policy gate:
  - same nuisance vector counts for baseline and candidate;
  - foreground/calibration parameters are declared by clik wrappers;
  - no global nuisance profiling yet;
  - candidate status: `fixed_nuisance_effective_candidate`.
- [x] Add high-l residual diagnostic report:
  - TT peak shifts: zero in tested bands;
  - TE zero shifts: zero in tested bands;
  - EE peak shifts: zero in tested bands;
  - residuals and smoothness scores exported;
  - non-overlap accounting included.
- [x] Add candidate nuisance sensitivity gate:
  - `lambda_T=-0.008` and `lambda_E=-0.02` remain frozen;
  - nuisance perturbations applied symmetrically to GR baseline and candidate;
  - non-overlap gains survive the tested nuisance grid;
  - TE cost remains small and EE remains non-degraded;
  - candidate status: `nuisance_sensitivity_checked_candidate`;
  - still not a profiled Planck candidate.
- [x] Run candidate local nuisance profiling gate:
  - same nuisance space, priors, bounds and optimizer for GR and candidate;
  - non-overlap combined profiled gain: `-5.1768`;
  - non-overlap decomposed profiled gain: `-5.9829`;
  - local profiled gains are favorable;
  - boundary hits detected for `calib_217T` and `gal545_A_217`;
  - `local_profiled_nuisance_effective_candidate = false`;
  - `profiled_planck_candidate = false`;
  - next blocker: boundary-safe profiling policy.
- [x] Add and run boundary-safe nuisance profiling gate:
  - no new Z4 physics and no retuning;
  - robust boundary-safe policies: `boundary_guarded`, `problem_nuisances_fixed`;
  - `boundary_guarded` gains: combined `-5.7058`, decomposed `-6.5223`;
  - `problem_nuisances_fixed` gains: combined `-13.1561`, decomposed `-12.0977`;
  - `boundary_safe_local_profiled_candidate = true`;
  - `profiled_planck_candidate = false`;
  - `full_planck_validation = false`.
- [x] Add candidate cosmology parameter policy gate:
  - standard cosmology parameters are fixed in the current spectra-table backend;
  - `lambda_policy = frozen_from_candidate_spec_after_internal_trials`;
  - no lambda retuning and no new Z4 physics;
  - policy gate passes as a documentation/guard rail.
- [x] Add candidate local cosmology profiling gate:
  - same cosmology/prior/optimizer rule is required for GR and candidate;
  - local cosmology profiling is intentionally blocked;
  - blocker: current backend consumes fixed spectra tables and cannot regenerate spectra under `omega_b/omega_cdm/H0/tau/As/ns` shifts;
  - `local_cosmology_profiled_candidate = false`;
  - `profiled_planck_candidate = false`;
  - `full_planck_validation = false`.
- [x] Add regenerative CAMB/Z4 backend gate:
  - current status: blocked;
  - `source_of_spectra = csv_fixed`;
  - CAMB-GR spectra are not regenerated per cosmology;
  - Z4 deltas are not regenerated per cosmology;
  - cache/provenance keys for cosmology/nuisance/lambda/backend versions are required before profiling;
  - local cosmology profiling remains forbidden.
- [x] Add regenerative CAMB-GR provider:
  - generates TT/TE/EE/C_phi_phi schema from CAMB for a cosmology point;
  - `lambda_T = 0`, `lambda_E = 0`;
  - `source_of_spectra = regenerated`;
  - cache/provenance manifest includes cosmology, nuisance, lambda, CAMB and backend hashes.
- [x] Add regenerative GR handshake gate:
  - `lambda_T = 0`, `lambda_E = 0`, Z4 disabled;
  - regenerated vector matches the safe CAMB-GR reference;
  - conventions recorded: `C_l` not `D_l`, lensed CMB spectra, `C_L^phiphi`, TE sign, ell indexing;
  - likelihood sanity checked by the official wrappers when run in official mode.
- [x] Add regenerative cache invalidation gate:
  - changing each standard cosmology parameter changes the cosmology/theory hashes;
  - spectra change under `omega_b`, `omega_cdm`, `H0`, `tau`, `A_s`, `n_s`;
  - stale CSV reuse remains forbidden.
- [x] Add regenerative frozen candidate replay gate:
  - `lambda_T = -0.008`, `lambda_E = -0.02`;
  - no retuning and no new physics;
  - checkpoint deltas replay at reference cosmology;
  - `z4_delta_source = reference_cosmology_replay`;
  - local cosmology profiling remains blocked until Z4 deltas regenerate per cosmology.
- [x] Add regenerative Z4 delta per cosmology gate:
  - effective closed-Boltzmann spectral deltas change under cosmology mutations;
  - delta cache key includes cosmology and lambda hashes;
  - no stale effective delta reuse;
  - strict source-level `delta_S_T_Z4` and `Pi` regeneration remains open;
  - local cosmology profiling remains blocked.
- [x] Add source-level Z4 delta regeneration gate:
  - strict gate remains blocked;
  - `delta_S_T_Z4` and `Pi_source_Z4` are not regenerated per cosmology;
  - no local cosmology profiling is allowed from effective spectral deltas alone.
- [x] Add regenerative temperature source delta gate:
  - source objects `W_acoustic`, `exp(-kappa)`, `deltaPhiDot+deltaPsiDot`, time grid and projection grid are regenerated per cosmology;
  - `delta_S_T_Z4_regenerated_per_cosmology = true` for the frozen `early_isw_only` temperature channel;
  - local cosmology profiling remains blocked until polarization/Pi source regeneration and strict replay pass.
- [x] Add regenerative polarization Pi source gate:
  - source objects `Theta_l`, `E_l`, `Pi_source_Z4`, TCA switch, opacity grid and time grid are regenerated per cosmology;
  - `Pi_source_Z4` is derived from multipoles, with no free `Theta2` tag and no direct TE/EE patch;
  - local cosmology profiling remains blocked until strict source-level replay passes.
- [x] Add strict source-level frozen candidate replay gate:
  - replay the frozen candidate with `z4_delta_source = strict_source_level_regenerated`;
  - compare high-l TT/TE/EE/TTTEEE and non-overlap totals against the checkpoint;
  - keep `profiled_planck_candidate = false` and `full_planck_validation = false`.
- [x] Add local cosmology profiling readiness gate:
  - GR handshake, cache invalidation, frozen replay and effective deltas are green;
  - source-level T/Pi regeneration and strict replay are required;
  - readiness now opens local cosmology profiling, not full Planck validation.
- [x] Add local cosmology+nuisance profiling gate:
  - profile GR and candidate over the same local cosmology grid and nuisance policy;
  - keep `lambda_T = -0.008`, `lambda_E = -0.02`, no retuning and no new physics;
  - combined high-l gain `-4.6204804254`, decomposed high-l gain `-4.2056083637`;
  - promote only `local_cosmology_nuisance_profiled_effective_candidate`, not full Planck validation.
- [x] Add carrier parameter degeneracy report:
  - focus parameter: `omega_cdm`;
  - 1D `omega_cdm` marginalization does not preserve the gain;
  - combined high-l gain after marginalization: `+0.6827240820`;
  - decomposed high-l gain after marginalization: `+0.9162249090`;
  - status: degeneracy detected, no Planck-profiled promotion.
- [x] Add local 2D carrier profiling gate:
  - tested `omega_cdm x A_s`, `omega_cdm x n_s`, `omega_cdm x H0`, `omega_cdm x omega_b`;
  - all tested pairs fail to preserve the frozen-candidate gain;
  - status: `local_2d_carrier_profiled_effective_candidate = false`.
- [x] Add carrier tangent projection gate:
  - project the frozen Z4 delta onto local GR/CAMB tangents for `omega_cdm`, `omega_b`, `H0`, `A_s`, `n_s`, `tau`;
  - parallel fraction: `0.9040080775`;
  - perpendicular fraction: `0.0959918908`;
  - dominant tangent direction: `A_s`;
  - orthogonal residual does not improve non-overlap Planck: combined `+18.6589`, decomposed `+18.2580`;
  - status: diagnostic complete, no Planck-profiled promotion.
- [x] Add carrier-degenerate candidate closure gate:
  - preserve the positive history: fixed-carrier, boundary-safe nuisance, and source-level regenerative gates passed;
  - close the final role as `diagnostic_archived`;
  - set `carrier_degenerate_effective_candidate = true`;
  - keep `profiled_planck_candidate = false` and `full_planck_validation = false`.
- [x] Add derived slip gate contract:
  - block free slip, free `eta(a,k)`, direct `C_l` patches and raw toy LOS;
  - keep `derived_slip_candidate_enabled = false` until a source-derived Z4/bimetric slip equation exists;
  - require source-level regeneration and carrier tangent projection before any Planck trial.
- [x] Derive the Z4/bimetric slip source equation needed by `P0EFTJanusZ4DerivedSlipGate`:
  - source operator: `Lap_TF(delta_slip_Z4) = -chi*(Pi_plus_TF + Pi_minus_TF)`;
  - closes the source equation, not the value-slip Green/normal-mode transport.
- [x] Add derived-slip scaffolding gates:
  - `BimetricScalarVariablesGate` declares plus/minus metric, fluid, projection, mixing and stress variables;
  - `TracelessSpatialSlipEquationGate` exposes source-level slip from the trace-free spatial equation;
  - `DerivedSlipRegenerationReadinessGate` remains blocked until value-slip transport is derived.
- [x] Add slip transport kernel gate:
  - requires either boundary Green transport or normal-mode transport;
  - keeps value-level `deltaSlip_Z4(k,tau)` unavailable until a causal normalized kernel is derived;
  - forbids Planck trials, free slip and free `eta(a,k)`.
- [x] Add boundary Green slip transport gate:
  - route selected: boundary Green transport;
  - kernel declared but not derived;
  - remains blocked until retarded support, fixed normalization, regularity and boundary jump conditions are closed.
- [x] Add boundary Green operator closure gate:
  - operator type selected: `boundary_normal`;
  - declares `L_slip_Z4 G_slip_Z4 = delta`;
  - blocks until boundary jumps, normalization, homogeneous-mode removal and regularity are derived.
- [x] Derive boundary-normal Green kernel transport:
  - solves finite-interval `L_slip_Z4 = -d_n^2 + k^2` with Z4 Dirichlet boundaries;
  - fixes normalization by the derivative jump and removes homogeneous mode by boundary conditions;
  - value-level `deltaSlip_Z4` transport is mathematically available, but Planck remains blocked.
- [x] Implement `DerivedSlipValueTransportGate`:
  - visible projection: `boundary_normal_derivative`;
  - Dirichlet boundary value is zero by construction;
  - value-level `deltaSlip_Z4` and `deltaSlipDot_Z4` are available, with Planck still blocked.
- [x] Implement `DerivedSlipSourceLevelRegenerationGate`:
  - reconstructs `deltaPhi_Z4` and `deltaPsi_Z4` from `deltaW_Z4` and derived `deltaSlip_Z4`;
  - regenerates temperature surface, early-ISW and Pi/polarization sources with slip;
  - logs normal orientation sign and keeps Planck blocked.
- [x] Implement `DerivedSlipCarrierTangentProjectionGate`:
  - compares surface, early-ISW, Pi and full-slip source signatures against GR/CAMB carrier tangents;
  - includes normal orientation flip as diagnostic-only;
  - keeps Planck trial and candidate promotion blocked.
- [x] Archive full derived-slip source as carrier-tangent:
  - full source is `A_s` dominated and not promotable;
  - Planck trial remains blocked.
- [x] Add surface-term orthogonality diagnostic:
  - surface term is orthogonal enough to inspect;
  - orthogonal residual remains blocked until SW consistency closes.
- [x] Add surface Sachs-Wolfe consistency blocker:
  - `g * deltaPsi_Z4` alone is not physical without photon monopole/Doppler closure;
  - next gate must derive photon-monopole SW closure.
- [x] Implement `DerivedSlipPhotonMonopoleSWClosureGate`:
  - forms `g * (deltaTheta0_Z4 + deltaPsi_Z4)`;
  - derives Doppler diagnostic from photon-baryon velocity response;
  - keeps visibility/recombination frozen and Planck blocked.
- [x] Decide whether closed full-surface remains less tangent than no-slip:
  - full-surface parallel fraction is `0.794`, better than no-slip `0.904` but only weakly improved;
  - no Planck trial yet.
- [x] Implement `DerivedSlipSurfaceDopplerDecompositionGate`:
  - separates SW-only, Doppler-only and full-surface carrier alignment;
  - confirms Doppler reintroduces tangency.
- [x] Implement `DerivedSlipSurfaceCarrierTangentProjectionGate`:
  - classifies the branch as `weak_orthogonal_diagnostic`;
  - keeps candidate promotion and Planck trial blocked.
- [x] Implement `DopplerTransportClosureRefinementGate`:
  - derives photon dipole and baryon velocity responses;
  - enforces tight-coupling/Euler guards;
  - keeps visibility/recombination frozen and no Doppler amplitude free.
- [x] Decide branch fate after refined Doppler classification:
  - refined full-surface parallel fraction is `0.834`, worse than prior `0.794`;
  - branch remains weak/carrier-tangent.
- [x] Archive weak surface branch:
  - SW-only orthogonal component exists;
  - physical Doppler-completed surface is not promotable;
  - Planck trial remains blocked.
- [x] Open two-sector Boltzmann dynamics:
  - declares plus/minus perturbation variables explicitly;
  - forbids `rho_eff`, direct `C_l` patches and raw toy LOS;
  - keeps Planck and spectra generation blocked.
- [x] Implement `TwoSectorConservationBianchiGate`:
  - declares plus/minus continuity, Euler and shear closure rows;
  - declares explicit zero exchange terms;
  - enforces projected Bianchi guard and separates gravitational sign from thermodynamic density sign.
- [x] Implement `TwoSectorInitialModeGate`:
  - declares plus/minus adiabatic, symmetric, antisymmetric Z4, relative isocurvature and projection modes;
  - enforces regular, constraint/Bianchi-compatible initial conditions;
  - forbids standard CAMB adiabatic forcing and `rho_eff` initial-condition collapse.
- [x] Implement `TwoSectorLinearEvolutionClosureGate`:
  - declares `X' = A_Z4(k,tau) X + S_Z4(k,tau)`;
  - evolves plus/minus fluid rows, metric constraints and projection rows;
  - keeps source regeneration, spectra and Planck blocked until stability checks.
- [x] Implement `TwoSectorStabilityEigenmodeGate`:
  - checks finite eigenvalues and no explosive real modes;
  - guards symmetric, antisymmetric Z4, relative isocurvature and projection modes;
  - allows source-level regeneration only, not spectra or Planck.
- [x] Implement `TwoSectorSourceLevelRegenerationGate`:
  - regenerates plus, minus, antisymmetric Z4 and projection sources;
  - exposes Weyl, monopole and Pi projected source diagnostics;
  - allows carrier-tangent projection only, not spectra or Planck.
- [x] Implement `TwoSectorCarrierTangentProjectionGate`:
  - projects Weyl, monopole, Pi and full two-sector diagnostics against GR/CAMB carrier tangents;
  - keeps spectra, Planck and promotion blocked.
- [x] Decide next action from two-sector tangent classification:
  - full two-sector diagnostic is `archive_fast`;
  - full parallel fraction is `0.998`, dominated by `A_s`;
  - no spectra or Planck trial.
- [x] Archive current two-sector full source as carrier-degenerate:
  - full source is `A_s` dominated and not promotable;
  - variables/conservation/modes/evolution/stability/source history is preserved.
- [x] Implement `TwoSectorSourceConstructionAuditGate`:
  - decomposes plus, minus, symmetric, antisymmetric Z4, relative-isocurvature, projection-only, Weyl, Theta0 and Pi sources;
  - no spectra or Planck trial is allowed.
- [ ] Decide whether any audited sub-component below `parallel_fraction < 0.7` deserves a separate gate.
- [x] Implement `ProjectionParityPreservationGate`:
  - compares value, normal-derivative, jump, membrane-weighted and mixed projections;
  - reports whether any projection preserves the Z4-odd antisymmetric mode without becoming carrier-tangent;
  - keeps spectra and Planck blocked.
- [x] Decide projection parity outcome:
  - no tested projection preserves a non-carrier-tangent antisymmetric mode;
  - best projection remains `parallel_fraction ~= 0.999`;
  - next required gate is `MinusSectorIndependentTransferGate`.
- [x] Implement `MinusSectorIndependentTransferGate`:
  - compares `T_minus` against best-fit `c*T_plus` for density, velocity, shear, Weyl, Theta0, Pi and projection source;
  - reports residual, phase lag and effective rank;
  - keeps spectra, Planck, projection retuning and free minus amplitude blocked.
- [x] Decide minus-sector transfer outcome:
  - no tested component has independent transfer rank;
  - density, velocity, shear, Weyl, Theta0, Pi and projection source remain rank-1 / amplitude-rescaling dominated;
  - next required work is deriving minus-sector microphysics, not trying Planck.
- [ ] Derive minus-sector microphysics:
  - independent sound speed, pressure, shear/free-streaming, thermal ratio or decoupling law;
  - must preserve conservation/Bianchi and forbid free normalization knobs.
- [x] Implement `MinusSectorMicrophysicsSpecificationGate`:
  - declares required non-amplitude mechanisms;
  - selects sound-speed/Jeans as first route;
  - forbids amplitude knobs, `rho_eff`, projection-only rescue, spectra and Planck.
- [x] Implement `MinusSectorSoundSpeedJeansGate`:
  - tests a fixed Jeans-profile minus-sector deformation;
  - reports transfer rank and carrier tangency before any observational use.
- [x] Decide sound-speed/Jeans outcome:
  - independent transfer rank appears for density/Weyl/Theta0/projection source;
  - all channels remain carrier-tangent (`parallel_fraction ~= 0.999`);
  - no component survives `parallel_fraction < 0.7`.
- [x] Implement `MinusSectorShearFreeStreamingGate`:
  - declares `sigma_minus` and an `F_l_minus` free-streaming hierarchy;
  - audits shear-only, free-streaming-only, Weyl anisotropic stress, Pi response and full channel;
  - keeps spectra, Planck, promotion and free amplitudes blocked.
- [x] Decide shear/free-streaming outcome:
  - Weyl anisotropic stress, Pi response and full channel get independent rank;
  - all remain carrier-tangent (`parallel_fraction ~= 0.998-0.999`);
  - no component survives `parallel_fraction < 0.7`.
- [x] Implement `MinusSectorThermalRatioGate`:
  - tests fixed `xi_T = T_minus / T_plus`;
  - audits thermal density, pressure, damping, decoupling proxy, Pi response and full channel;
  - keeps free thermal-ratio fitting, spectra and Planck blocked.
- [x] Decide thermal-ratio outcome:
  - independent transfer rank appears in several channels;
  - all channels remain carrier-tangent (`parallel_fraction ~= 0.997-0.999`);
  - no component survives `parallel_fraction < 0.7`.
- [x] Add `MinusSectorDecouplingLawGate` blocker:
  - requires a derived minus-sector visibility/opacity/drag/recombination law;
  - forbids free decoupling shifts and visibility patches.
- [x] Freeze/archive current two-sector CMB/Z4 branch:
  - status: `diagnostic_archived`;
  - projection, slip/surface, sound-speed/Jeans, shear/free-streaming and thermal-ratio routes remain carrier-tangent;
  - no spectra, Planck, promotion, retuning, projection tweaks or new effective CMB/Z4 gates on this branch.
- [ ] Reopen only if an action-derived minus-sector decoupling/recombination law is available.

## Unique Z4 master equation track

Status: archived diagnostic track. It is not part of the active Z2/Sigma model.

Rationale:
- downstream additions built separately keep becoming carrier-tangent;
- archived failures include slip, surface/Doppler, two-sector projection, sound-speed/Jeans, shear/free-streaming and thermal-ratio routes;
- historical lesson: independent downstream corrections failed; any future
  non-Z2 extension would need one upstream generator, but this is not active.

Policy:
- no Planck;
- no spectra;
- no retuning;
- no free `eta`;
- no free slip;
- no free projection coefficient;
- no independent Doppler/Pi/minus-sector amplitude;
- no `rho_eff` shortcut;
- no direct `C_l` patch;
- no raw toy LOS.

Required formal gates:
- [x] `P0EFTJanusZ4UniqueEquationMasterGate`:
  - declare master variable `U_Z4`;
  - declare master operator `L_Z4`;
  - declare source `J_Z4`;
  - declare Z4 parity;
  - declare orbifold/boundary conditions;
  - declare GR limit;
  - set `master_equation_solved = false` until actually derived;
  - keep spectra and Planck blocked.
- [x] `P0EFTJanusZ4MasterReconstructionGate`:
  - reconstruct `Phi_plus`, `Psi_plus`;
  - reconstruct `Phi_minus`, `Psi_minus`;
  - reconstruct `delta_plus`, `theta_plus`, `sigma_plus`;
  - reconstruct `delta_minus`, `theta_minus`, `sigma_minus`;
  - reconstruct `Theta0_Z4`;
  - reconstruct `v_gamma_Z4` / Doppler;
  - reconstruct `Pi_Z4`;
  - reconstruct `Weyl_Z4`;
  - reconstruct observable projection;
  - mark any missing map as `blocked_until_master_reconstruction`, not silently free.
- [x] `P0EFTJanusZ4MasterConstraintConsistencyGate`:
  - check Bianchi consistency;
  - check plus/minus conservation;
  - check trace-free slip consistency;
  - check Doppler/continuity consistency;
  - check `Pi` comes from multipoles;
  - check projection Z4 compatibility;
  - check GR limit;
  - keep spectra and Planck blocked.
- [x] `P0EFTJanusZ4MasterToObservableMapGate`:
  - define `S_T,Z4 = F_T[U_Z4]`;
  - define `S_E,Z4 = F_E[U_Z4]`;
  - define `S_lens,Z4 = F_lens[U_Z4]`;
  - prove Doppler, Theta0, Pi, slip and minus-sector variables use the same `U_Z4`;
  - forbid independent downstream source patches.
- [x] `P0EFTJanusZ4MasterCarrierTangentProjectionGate`:
  - project the master-derived signal against GR/CAMB carrier tangents;
  - report dominant carrier direction;
  - compare against archived branches;
  - success threshold: `parallel_fraction < 0.7`;
  - strong threshold: `parallel_fraction < 0.5`;
  - if `parallel_fraction > 0.8`, archive current master-equation ansatz before any Planck gate.
- [x] Decide first unique-master ansatz outcome:
  - `parallel_fraction = 0.9973`;
  - dominant carrier direction is `tau`;
  - current master diagnostic ansatz does not beat archived patchwork branches;
  - no spectra or Planck trial is allowed.
- [x] Add `P0EFTJanusZ4MasterAnsatzRevisionScanGate`:
  - scans internal non-observational master ansatz shapes;
  - reports best carrier-tangent projection;
  - keeps lambda retuning, spectra, Planck and promotion blocked.
- [x] Decide revised master ansatz outcome:
  - best ansatz is `localized_transition`;
  - `parallel_fraction = 0.176`;
  - passes both `<0.7` and `<0.5` internal carrier-tangent thresholds;
  - still no spectra or Planck.
- [x] Add `P0EFTJanusZ4MasterSourceLevelRegenerationGate`:
  - regenerates `U_Z4`, `S_T`, `S_E`, `S_lens`, Doppler, Theta0, Pi, slip and minus-sector variables from the selected master ansatz;
  - keeps all sources tied to the same `U_Z4` hash;
  - keeps spectra and Planck blocked.
- [x] Add `P0EFTJanusZ4MasterConstraintClosureAuditGate`:
  - closes Doppler/continuity, Theta0, Pi, slip, lensing, temperature, polarization and minus-sector consistency against the same `U_Z4`;
  - keeps spectra and Planck blocked.
- [x] Add `P0EFTJanusZ4MasterSourceCarrierTangentReplayGate`:
  - replays the regenerated source-level payload against GR/CAMB carrier tangents;
  - verifies whether the source map preserves the `<0.7` carrier threshold;
  - keeps spectra and Planck blocked.
- [x] Decide source carrier replay outcome:
  - regenerated source replay gives `parallel_fraction = 0.191`;
  - passes `<0.7` and `<0.5`;
  - next gate may check diagnostic spectra readiness, but Planck remains blocked.
- [x] Add `P0EFTJanusZ4MasterDiagnosticSpectraReadinessGate`:
  - allows internal diagnostic spectra generation only;
  - keeps official Planck, likelihood evaluation, promotion, retuning and nuisance refit blocked.
- [x] Add `P0EFTJanusZ4MasterDiagnosticSpectraGenerationGate`:
  - writes internal GR and GR+master-Z4 diagnostic spectra;
  - replays carrier projection after CSV serialization;
  - keeps official Planck, likelihood evaluation, promotion and retuning blocked.
- [x] Add `P0EFTJanusZ4MasterDiagnosticShapeReportGate`:
  - reports TT/TE/EE ratio stats, peak shifts and zero-count changes;
  - remains diagnostic-only and forbids likelihood evaluation.
- [x] Add `P0EFTJanusZ4MasterPreLikelihoodLockGate`:
  - blocks likelihoods when diagnostic spectra have zero-crossing or large fractional shape artifacts;
  - current lock is active because TT/EE acquire extra zero crossings.
- [x] Archive master shape regularization instead of revising it under the
  active Z2/Sigma model.

Completion rule:
- [x] Only if the master-derived signal passes carrier-tangent projection, open a controlled diagnostic source-level regeneration gate.
- [x] Observational gates for this Z4 branch are archived under the active
  Z2/Sigma model.
- [x] Enforce post-checkpoint freeze rule:
  - checkpoint: `8ce53806`;
  - no new Z4 physics or parameter retuning is allowed until standalone high-l TE/EE likelihood coverage is acquired;
  - rerun the frozen candidate unchanged before any new mechanism is opened.
- [x] Add standalone TE/EE handshake gate:
  - checks required: `C_l/D_l`, units, TE sign, `ell` indexing, nuisance vector, foreground handling, GR reference sanity;
  - current status: blocked because standalone high-l TE/EE are unavailable;
  - full high-l decomposition trial remains forbidden;
  - frozen candidate invariants remain enforced.
- [x] Add the CMB primordial imprint lock:
  - TT acoustic source + SW/ISW;
  - Theta2 + physical visibility transport;
  - Weyl/lensing membrane projection.
- [x] Close the internal CMB primordial imprint lock without running Planck:
  - all block statuses true in `p0_eft_janus_z4_primordial_imprint_lock.json`;
  - next allowed action is the official non-compressed Planck gate.
- [ ] Re-run SDSS/eBOSS `f_sigma8` only after the bi-sector equations are fixed.
- [ ] Re-run DESI BAO with the derived `r_d`, not a fitted ruler.
- [x] Re-run Planck after the internal primordial-imprint lock:
  - background;
  - perturbations;
  - lensing;
  - visibility/recombination assumptions.
- [ ] Fix the post-lock Planck rejection:
  - current Planck gates consume the safe CAMB-GR baseline provider;
  - native Z4 spectra are not used by default;
  - toy native source engine remains blocked;
  - high-l TE/EE standalone clik files are unavailable locally.
- [x] Run explicit observed Planck diagnostic for master v2:
  - observed trial executed;
  - non-overlap combined high-l = `9183.131824821805`;
  - non-overlap decomposed high-l = `9609.043119904283`;
  - branch rejected, dominated by high-l acoustic shape.
- [x] Add `MasterObservedFailureMapV2Gate`:
  - locks the observed v2 rejection;
  - keeps candidate promotion, retuning, new physics, and full Planck validation blocked.
- [x] Add `MasterHighLAcousticFailureAutopsyGate`:
  - decomposes TT/TE/EE peak shifts, TE zero shifts and damping-tail residuals;
  - records that current spectra are lensed-total only, so unlensed/source split is still open;
  - keeps Planck retry, retuning, new physics and promotion blocked.
- [x] Add `MasterPhotonBaryonMatchingGate`:
  - verifies the declared `U_Z4 -> Theta0/Doppler/Pi/PhiPsi` mapping;
  - inherits the acoustic phase failure and blocks spectra/Planck retry;
  - requires upstream photon-baryon rederivation.
- [x] Add `MasterSourceComponentDiagnosticSpectraGate`:
  - writes diagnostic-only `surface_SW`, `early_ISW`, `Doppler`, `polarization_Pi`, `lens_Weyl` spectra;
  - no observed likelihood, no promotion, no retuning.
- [x] Add `MasterPhotonBaryonAcousticCalculatorGate`:
  - starts a calculator rebuild with oscillator phase and Doppler quadrature;
  - writes `p0_eft_janus_z4_master_acoustic_calculator_payload.json`;
  - remains diagnostic-only and blocks spectra/Planck.
- [x] Add solver implementation checkpoint:
  - `MasterAcousticCalculatorComponentSpectraGate`;
  - `MasterAcousticCalculatorShapePhaseDampingGate`;
  - `MasterSolverProvenanceManifestGate`;
  - `MasterSolverImplementationReadinessGate`;
  - `solver_implemented = true` only for internal diagnostic CMB generation.
- [x] Add unlensed/lensed and future observational readiness:
  - `MasterUnlensedLensedSplitGate`;
  - `MasterLensingRemapPolicyGate`;
  - `MasterFutureObservedPlanckDiagnosticReadinessGate`;
  - future observed diagnostic allowed only under split/provenance/non-retuning guards;
  - full Planck validation and promotion remain false.
- [x] Add complete Z4 CMB solver stack:
  - Z4 Boltzmann evolution core;
  - visibility/recombination handling;
  - Weyl line-of-sight lensing with unlensed Cl, C_L phiphi and lensed TT/TE/EE;
  - per-cosmology regeneration checks;
  - likelihood-ready theory vector gate with Planck validation still false.
- [x] Add GR-reference convention handshake:
  - calibrates proxy theory vector to `dimensionless_Cl_CAMB_convention_calibrated`;
  - checks `C_l` convention, ell indexing and channel lengths;
  - still no Planck validation or promotion.
- [ ] Archive the current master-v2 CMB mapping or derive an unlensed/source-level backend.

## Active Z2/Sigma F_a=0 route

- [x] Close local matter/Holst Sigma flux subroute:
  - perfect-fluid tangential flux zero from `u.n=0` and `e.n=0`;
  - torsionless local Holst/Nieh-Yan Sigma flux slot `E_HolstNiehYan=0`;
  - writes the perfect-fluid radial `E_matterFlux=0` manifest;
  - no claim about off-Sigma bulk Holst stress or full Sigma transparency.
- [x] Close local MIT projector algebra:
  - unit-normal Clifford action;
  - idempotent/self-adjoint reflecting projector;
  - normal-current zero identity conditional on the boundary spinor satisfying the projector.
- [ ] Derive the physical reflecting spinor boundary condition:
  - plus/minus spinor bundles on the resolved tunnel;
  - boundary spinor restriction to Sigma;
  - proof that the active boundary spinor satisfies the fixed reflecting projector;
  - then feed `normal_dirac_current_zero` to full Sigma transparency.
- [ ] Or derive the Janus/Z2 normal-current cancellation route:
  - sheet-exchange normal reversal is ready;
  - conditional Dirac-current parity algebra is ready from a spinor intertwiner;
  - local Sigma `U_Z2^Sigma = B_n` is ready for Clifford/adjoint algebra;
  - extend local `U_Z2^Sigma` to the resolved-tunnel Pin lift;
  - prove physical spinor equivariance `psi_- = U_Z2 psi_+`;
  - fix the projected-current orientation sign from the action;
  - prove or reject `J_n^Z2Sigma=0` without imposing MIT reflection.

## Active Z2/Sigma counterterm closure

- [x] Correct the counterterm attack order:
  - detected the circular dependency `R_Sigma -> embedding -> delta_K -> counterterm -> R_Sigma`;
  - forbids using the active embedding as prerequisite for the symbolic
    counterterm primitive;
  - new non-circular route: derive `L_ct` first in the local boundary basis
    `(h_ab, K_ab, torsion pullback, Immirzi/radion, Z2 sign)`, then evaluate it
    radially after an `R_Sigma` grid/certificate exists.
- [x] Materialize the symbolic local primitive:
  - writes `counterterm_symbolic_local_primitive.json`;
  - records `L_ct = - integral_gamma alpha_res`;
  - explicitly keeps `coefficient_expansion_explicit = false` and
    `radial_profile_ready = false`.
- [x] Close local tetrad transport for the counterterm channel:
  - writes `counterterm_tetrad_transport_closure.json`;
  - derives `h_ab=R_Sigma^2 q_ab`, `K_ab=R_Sigma q_ab`,
    `partial_R K_ab=q_ab`, `K=3/R_Sigma`, and
    `partial_R K=-3/R_Sigma^2`;
  - closes the torsionless active pullback branch from
    `torsion_pullback_components_inputs.json`;
  - does not write `L_ct`, `E_counterterm`, or an `R_Sigma(a)` solution.
- [ ] Derive symbolic `L_ct` in the allowed local density basis:
  - reuse the old Sigma nonlinear residual closure only as a uniqueness/cancellation
    statement;
  - do not promote it to a radial value until coefficients are explicit;
  - extract the tetrad residual one-form, prove exactness, integrate primitive.
- [x] Close `delta_e -> delta_K` without radius values for the counterterm-local
  branch:
  - symbolic Gaussian collar gives the allowed-basis transport;
  - full active embedding values remain deferred until `R_Sigma(a)` exists.
- [x] Close torsion-pullback symbolic variation for the counterterm-local branch:
  - Cartan formula and pullback/variation commutation are ready;
  - active local torsionless unit-q components close the current allowed-basis
    counterterm transport;
  - nonzero Holst torsion remains a separate physical branch, not assumed here.
- [x] Reduce the active torsion residual coefficient:
  - writes `counterterm_residual_coefficients_partial.json`;
  - derives `R_T^A=0` for the active torsionless Sigma branch;
  - uses only active torsion pullback, irreducible torsion, and
    `rsigma_E_HolstNiehYan` payloads.
- [x] Reduce the radial counterterm formula symbolically:
  - writes `counterterm_radial_projection_formula.json`;
  - derives `partial_R L_ct = -(2 R_Sigma R_h^{ab} q_ab + R_K^{ab} q_ab + R_chi partial_R chi)`;
  - derives `E_counterterm = partial_R(sqrt|h| L_ct)`;
  - does not invent `R_h`, `R_K`, `R_chi`, `R_Sigma`, or the `L_ct` integration constant.
- [x] Add the concrete `L_ct` radial profile calculator:
  - consumes `counterterm_residual_scalar_contractions_inputs.json`;
  - writes `counterterm_lct_radial_profile.json` only when scalar contractions
    and the `L_ct` integration constant are fixed;
  - feeds the existing strict density-variation route to `rsigma_E_counterterm`.
- [x] Add the tensor-to-scalar residual contraction assembler:
  - consumes active `q_ab`, `R_Sigma`, `R_h_ab`, `R_K_ab`, and
    Immirzi/radion scalar residual payloads;
  - writes `counterterm_residual_scalar_contractions_inputs.json`;
  - accepts active radius certificates using either `R_Sigma_of_a` or
    normalized `R_Sigma_values`;
  - current active run confirms `q_ab` and the torsionless Immirzi contraction
    are present.
- [x] Close the torsionless Immirzi scalar contraction:
  - writes `counterterm_immirzi_residual_scalar_inputs.json`;
  - derives `R_chi partial_R chi = 0` because the active torsionless
    Holst/Nieh-Yan pullback has no Immirzi radial contribution;
  - does not claim that the full `R_chi(a)` or `partial_R chi(a)` profile is
    solved.
- [x] Add a non-fit residual-tensor calculator from explicit local density:
  - consumes active `counterterm_local_density_action_inputs.json`;
  - differentiates `L_ct_expression` on the isotropic Sigma branch;
  - writes `counterterm_metric_residual_tensor_inputs.json` and
    `counterterm_extrinsic_residual_tensor_inputs.json`;
  - currently blocks because the active local counterterm density/action is not
    derived.
- [x] Materialize the current `L_ct` density decision:
  - checks GHY/Brown-York, pure Holst/Nieh-Yan, volume-solder/logdet, and
    transgression routes;
  - writes `counterterm_local_density_action_obstruction.json`;
  - does not write a fake `counterterm_local_density_action_inputs.json`;
  - now identifies the minimal missing physical input as the explicit
    coefficient expansion from the active Sigma counterterm boundary action.
- [x] Split pulled-dust action from pulled-Sigma-counterterm action:
  - records that the existing B4vol/pulled-dust chain is conditionally available;
  - prevents using the dust/matter action as the Sigma counterterm action;
  - keeps `counterterm_local_density_action_inputs.json` forbidden until an
    explicit `S_ct[Sigma]` boundary functional is written and reduced.
- [x] Write the symbolic Sigma counterterm boundary action:
  - defines `S_ct[Sigma] = integral_Sigma sqrt|h| L_ct(h,K,T_pullback,chi,epsilon_Z2)`;
  - fixes the measure as `dmu_Sigma = d^3y sqrt_abs_h`;
  - records the non-duplication role relative to Cartan-GHY, Holst/Nieh-Yan,
    matter/dust and tunnel-junction terms;
  - fixes the additive constant symbolically by `L_ct(reference_residual_zero_throat)=0`;
  - still forbids `counterterm_local_density_action_inputs.json` until the
    explicit coefficient expansion is derived.
- [x] Add the coefficient-expansion obligation gate:
  - consumes the symbolic `S_ct[Sigma]` boundary action;
  - records known partial closures `R_T^A=0` and `R_chi partial_R chi=0`;
  - identifies `R_h_ab` and `R_K_ab` from `delta S_ct` as the live blocker;
  - keeps local density action inputs forbidden.
- [x] Derive the measure-aware coefficient formula:
  - `R_h_ab = -(1/2 h^ab L_ct + partial L_ct/partial h_ab)`;
  - `R_K_ab = -partial L_ct/partial K_ab`;
  - `R_chi = -partial L_ct/partial chi`;
  - does not invent the still-missing explicit `L_ct_expression`.
- [x] Attempt explicit `L_ct_expression` derivation from the closed `S_ct` layer:
  - records that uniqueness/cancellation plus the variation formula are not
    enough to determine a local expression;
  - forbids alpha/beta ansatz, GHY reuse, matter-action reuse and observational
    fitting;
  - moves the precise blocker to explicit `alpha_res` components and field-space
    exactness.
- [x] Attempt `alpha_res` extraction:
  - writes `counterterm_alpha_res_partial.json`;
  - records torsion and Immirzi radial contractions as known on the active
    torsionless branch;
  - identifies tetrad residual coefficients `R_h_ab/R_K_ab` as the first concrete
    blocker before full one-form decomposition.
- [x] Attempt tetrad residual value extraction:
  - confirms tetrad transport and variation formulas are closed;
  - confirms the current nonlinear Sigma closure is boolean-only;
  - blocks because it does not emit `alpha_res_components`, `R_h_ab`, `R_K_ab`,
    or `L_ct_expression`.
- [x] Refine the nonlinear Sigma closure source gate:
  - keeps cancellation/uniqueness closed;
  - emits the `alpha_res` component schema:
    metric tetrad, extrinsic tetrad, torsion pullback, Immirzi/radion,
    connection, spinor, embedding and matter-flux;
  - keeps `alpha_res_component_values_available = false`;
  - records the next source-level obligation as `emit_alpha_res_component_values`.
- [x] Add the Janus/Z2 odd-residual bypass route:
  - tests whether `tau_Z2^* alpha_res = - alpha_res` could imply quotient
    cancellation and `E_counterterm=0`;
  - keeps the route blocked because anti-invariance of `alpha_res` is not proved.
- [x] Expand the Z2 anti-invariance obligation channel by channel:
  - confirms the route is `credible_but_blocked`, not closed;
  - uses available Z2 normal reversal, component schema and torsionless Holst
    boundary flux;
  - proves the conditional Lean bridge: componentwise odd emitted components
    imply `alpha_res` anti-invariance;
  - blocks on componentwise parity proofs, paired residual support,
    matter/stress equivariance, spinor-current parity and explicit values for
    tetrad/connection/chi channels;
  - forbids treating quotient cancellation as proved before
    `tau_Z2^* alpha_res_i = - alpha_res_i` is verified componentwise.
- [x] Isolate tetrad component parities:
  - proves the variation-side parity obligations:
    `delta h_ab` is Z2-even and `delta K_ab` is Z2-odd;
  - blocks the full `alpha_h/alpha_K` parity proof on coefficient parities:
    `R_h_ab` must be Z2-odd and `R_K_ab` must be Z2-even;
  - keeps `E_counterterm=0` by quotient blocked until those coefficient
    parities are derived from explicit component values.
- [x] Derive coefficient parities conditionally from odd Sigma density:
  - from `R_h_ab = -(1/2 h^ab L_ct + partial L_ct/partial h_ab)` and even
    `h_ab`, an odd `L_ct` implies odd `R_h_ab`;
  - from `R_K_ab = -partial L_ct/partial K_ab` and odd `K_ab`, an odd `L_ct`
    implies even `R_K_ab`;
  - keeps the route blocked on proving `tau_Z2^* L_ct = -L_ct`;
  - records that `E_counterterm=0` is only the quotient-cancellation bypass,
    not a required model condition.
- [x] Test the `L_ct` Z2-odd density route:
  - `L_ct = -integral alpha_res` plus zero-residual integration constant gives
    `tau_Z2^* L_ct = -L_ct` only after `alpha_res` anti-invariance is already
    proved;
  - using `L_ct` oddness to prove the tetrad components of `alpha_res` is
    circular;
  - the non-circular options are now explicit `L_ct_expression` parity or a
    derived nonzero `E_counterterm(a)` route.
- [x] Add a toy exact finite-throat diagnostic:
  - uses `h_ab=R^2 q_ab`, `K_ab^+=+R q_ab`, `K_ab^-=-R q_ab`;
  - confirms linear `K` terms are Z2-odd, while `K^2` and intrinsic curvature
    terms are Z2-even;
  - shows point-collapse power-law integrals can vanish as `R -> 0`;
  - keeps the result toy-only and not an active counterterm proof.
- [x] Add a minimal torsionless density basis diagnostic:
  - filters the candidate local basis to `epsilon_Z2*K`, `K^2`, and `R[h]`;
  - removes the constant by zero-throat normalization;
  - excludes torsion and Immirzi/radion gradient terms from the minimal
    torsionless branch;
  - shows the three coefficients are not solvable from symmetry alone;
  - next required constraints are `R_h` trace and `R_K` trace.
- [x] Vary the minimal density basis on the round-throat toy:
  - `sqrt(h)L_min = sqrt(q)*(3*c1*epsilon_Z2*R^2 + (9*c2+6*c3)*R)`;
  - `E_counterterm = partial_R(sqrt(h)L_min)`;
  - imposing toy `E_counterterm=0` for all `R` gives `c1=0` and
    `3*c2+2*c3=0`;
  - one coefficient remains free, so active `R_h/R_K` trace targets are still
    required.
- [x] Test both non-circular counterterm routes:
  - active trace route remains blocked because no active `R_h_trace/R_K_trace`
    target payload exists;
  - nonzero `E_counterterm` route is available only parametrically as
    `E_ct(R)=sqrt(q)*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)`;
  - numeric promotion still requires `c1,c2,c3`, `R_Sigma(a)` and volume
    normalization;
  - explicit policy: do not claim `E_counterterm=0` and do not fit
    `c1,c2,c3`.
- [x] Formalize the M30/S_cross counterterm blocker:
  - `P0EFTJanusZ2SigmaSCrossM30BoundaryReductionAuditGate` records that
    M15/M30 provide the Janus two-layer/bivariational context but not an
    explicit Sigma-local `S_cross` pullback or `phi/L` transport law;
  - under strict Z2 descent, the bulk M30 force cancels on Sigma, so it cannot
    source a nonzero `L_ct`;
  - nonzero counterterm closure still requires an independent tunnel-defect
    action or active `R_h_trace/R_K_trace` targets.
- [x] Reduce the local Sigma flux slot where possible:
  - `MatterFluxTransparencyInputWriterGate` now accepts the active local route
    `perfect-fluid tangential flux zero + torsionless Holst/Nieh-Yan boundary
    flux zero`;
  - this does not claim full off-Sigma bulk-stress projection;
  - `HolstNiehYanComponentFromInputsGate` can materialize a zero FLRW Holst
    component from the active torsionless radial identity;
  - `MatterFluxTransparencyInputWriterGate` can use the active Holst-zero
    component grid when the complete non-matter FLRW grid is not assembled yet;
  - `MatterFluxZeroComponentFromTransparencyGate` and
    `RSigmaMatterFluxRadialTermFromTransparencyGate` now write
    `matter_flux_zero_components.json` and `rsigma_E_matterFlux.json`;
  - remaining FLRW blockers are counterterm component and active dimensionful
    background scalars. The PT67 subroute now supplies a strict zero
    Cartan/GHY component from PT-transported `DeltaK=0`.
  - Cartan/GHY must not be set to zero by naive Z2 symmetry: with the active
    projective convention `eps_Z2=-1`, `K_-=-K_+` gives
    `DeltaK=K_+ - K_- = 2K_+`, not zero.
  - PT67 is a separate transport convention: `dt -> -dt`, `dr -> dr`, and
    screen transport give `DeltaK_TT=0` and `DeltaK_screen_trace=0`; this is
    not the standard outward-normal Israel cut-and-paste jump.
  - `CartanGHYComponentFromDeltaKInputsGate` now records that the projective
    collar ratio `R_Sigma/ell=1` is ready but insufficient for `DeltaK`; an
    absolute embedding/radius certificate is still required.
- Z2 cover master-action branch status:
  - projected plus/minus equations are written from one cover action target,
    not from two independent sector actions;
  - cross-measure transport is now active on the Sigma-restricted metric data,
    with `B_minus_to_plus = B_plus_to_minus = 1` on the current grid;
  - paired Bianchi balance is formulated and measure transport is ready;
  - closure still blocks on `sigma_source.json`, which in turn needs
    `sigma_alpha_h_inputs.json`, i.e. the same unresolved surface-HK
    coefficients/geometry route;
  - Lean ledger:
    `P0EFTJanusZ2CoverBianchiSigmaSourceFrontierGate` records that this is
    not a full Bianchi closure until the Sigma source is supplied.
- MPLA singularity paper extraction:
  - `MPLA_singularity_elimination_local_model` is now recorded as an auxiliary
    local Schwarzschild-throat model with
    `R(rho)=R_s*(1+log(cosh(rho)))`;
  - it gives a regular Z2 throat diagnostic:
    `R_Sigma/R_s=1`, `R'(0)=0`, `R''(0)/R_s=1`;
  - it supports the Z2 fold/orientation/mass-inversion reading, but it does not
    fix the absolute scale `R_s` or derive counterterm coefficients.
- Surface-action no-extension decision:
  - `P0EFTJanusZ2SigmaSurfaceActionOrNoGoGate` combines MPLA throat,
    projective ratio, Souriau charge, flux transparency and the counterterm chain;
  - current inputs underselect a unique active `L_Sigma(h,K,...)`;
  - `E_counterterm` and `sigma_alpha_h` remain open unless a genuine local Sigma
    density, boundary Hamiltonian variation, trace residual input, or explicit
    surface-action extension is supplied.
- Active pivot after reference review:
  - do not change the model: keep `Z2_tunnel_Sigma`;
  - change the route: start from the published bimetric bulk action plus Bianchi
    source-slot reduction before trying to invent a local Sigma counterterm;
  - next derivation order is interaction tensor slots -> reduced Bianchi closure
    -> transport to Sigma -> decide whether any extra Sigma surface term remains.
- Published interaction slots:
  - `P0EFTJanusZ2PublishedInteractionSlotsGate` maps the PDF action terms to
    active slots `T_plus`, `T_minus`, `T_minus_to_plus`, `T_plus_to_minus` and
    determinant bridges `B_minus_to_plus`, `B_plus_to_minus`;
  - the gate intentionally blocks Sigma transport until a reduced Bianchi closure
    or complete nonlinear interaction tensor is derived.
- Published FLRW Bianchi reduction:
  - homogeneous dust scalar-density sector is closed with determinant/lapse guards;
  - this is a valid reduced sector, not a generic nonlinear interaction tensor and
    not a Sigma junction/source closure.
- Published stationary SO(3)/TOV/Newtonian Bianchi reduction:
  - same-sector attraction and opposite-sector repulsion are recorded as the
    reduced compact-object sign sector;
  - determinant-ratio unity and Bianchi closure are only asymptotic/reduced;
  - this is not a generic nonlinear interaction tensor, not a Sigma source, and
    not an `R_Sigma(a)` certificate.
- SO(3) throat embedding manifest:
  - MPLA radius law gives a Z2-even minimal throat stencil
    `R(rho)=R_s*(1+log(cosh(rho)))`;
  - this supplies a stationary SO(3) embedding skeleton for Sigma;
  - metric functions, Christoffels, unit normals and `DeltaK_s/DeltaK_tau`
    remain open.
- Signed Schwarzschild SO(3) metric diagnostic:
  - published exterior blocks reduce to `f_epsilon(R)=1-epsilon*R_s/R`;
  - same-sign attractive block has `f(R_s)=0`, while opposite-sign repulsive
    block has `f(R_s)=2`;
  - the standard exterior-coordinate thin-shell `K_ab` formula is therefore
    degenerate at the throat and cannot close active `DeltaK`;
  - next concrete route is a regular throat collar/Kruskal-like chart at `R=R_s`,
    or diagnostic-only tests at `R>R_s`.
- Regular SO(3) throat collar frontier:
  - active regular Sigma branch needs a non-degenerate `(T,rho)` collar block
    `A(rho), B(rho), C(rho)`;
  - MPLA degenerate bridge interpretation is kept diagnostic-only because it can
    conflict with regular `h_ab`, `K_ab`, and `sqrt|h|` assumptions;
  - `DeltaK` can only be derived after the regular collar functions are derived
    from the Z2 bimetric field equations.
- Eddington/PT cross-term throat diagnostic:
  - chapter 6 supplies the useful clue: keep a `dr dt` cross term;
  - in `(T,R)` coordinates, the block
    `ds^2=(1-R_s/R)dT^2 - 2(R_s/R)dT dR - (1+R_s/R)dR^2`
    has determinant `-1`, so the bulk chart is regular at `R=R_s`;
  - however the induced `R=R_s` throat is null, and the even fold
    `R(rho)` with `R'(0)=0` degenerates the `(T,rho)` block;
  - therefore this is a null-Sigma/PT-bridge branch, not a closure of the
    current regular `h_ab,K_ab` counterterm pipeline.
- Null Sigma / PT bridge branch:
  - explicit branch facade: `JanusFormal.NullSigmaPTBridge`;
  - source alignment follows chapter 6/7 and EPJC summary:
    retained `dr dt`, one-way bridge, PT-symmetric sheets, orientation/time
    reversal, Souriau mass-energy inversion, projective/tubular topology;
  - regular `h_ab,K_ab`, GHY/Israel/Cartan and `L_ct(h,K,...)` are forbidden on
    this branch;
  - next concrete objects are null-boundary variables
    `l`, `n`, `q_AB`, `theta`, `sigma_AB`, `kappa` and a null junction/Bianchi
    balance.
- Parallel branch status:
  - regular branch algebra now isolates the hard condition:
    `A(0) != 0` is required for invertible induced `h_ab`; the Eddington/PT
    horizon has `A(0)=0` and is therefore excluded from regular `h,K`;
  - null branch declares concrete horizon variables:
    `l=(1,0,0,0)`, `n=(-1,1,0,0)`, `l.n=-1`, `q_AB=R_s^2 dOmega^2`,
    `theta_l=0`, `shear=0`, `kappa_l=1/(2R_s)`;
  - null boundary density is now identified as `sqrt(q) kappa_l`, with
    generator-rescaling ambiguity and corner/joint variation slots recorded;
  - the SO(3) radial variation of `sqrt(q) kappa_l` is now reduced:
    for `R_s=1`, `delta[sqrt(q) kappa_l]/sin(theta) = 0.5 deltaR_s`;
  - the canonical PT joint term is reduced under `l_+ . n_- = -1`: the
    logarithmic joint density and its variation vanish;
  - Barrabes-Israel data are reduced only on the plus side:
    `C_TT=1/(2R_s)`, `q^AB C_AB=-2/R_s`; null-shell stress still needs a
    derived inter-sheet jump `[C_ab]`;
  - source check against chapter 6.7 shows a better active route: the PT
    transfer metric with sign-flipped integration constant has at `r=a`
    `g_tt=2`, `g_rr=0`, `det(T,r)=-1`, so the induced surface is not
    degenerate; therefore the null-shell branch is exhausted as diagnostic and
    should not be promoted. Next active route: derive `h_ab,K_ab` for the
    regular chapter-6.7 PT transfer surface.
- Chapter-6.7 regular PT transfer surface:
  - metric route encoded as
    `A=1+R_s/r`, `B=1-R_s/r`, `C=epsilon R_s/r`, with
    `epsilon=-1` on the first sheet and `epsilon=+1` on the second;
  - at `r=R_s`: `det(T,r)=-1`, `h_TT=2`, `h_AB=-R_s^2 gamma_AB`,
    so the induced surface is non-degenerate and the regular `h,K` pipeline is
    locally allowed;
  - local unit normal and extrinsic curvature are derived:
    `n=dr/sqrt(2)`, `K_TT=1/(sqrt(2)R_s)`,
    `K_AB=sqrt(2)R_s gamma_AB`;
  - PT gluing orientation is now fixed by `dt -> -dt`, `dr -> dr`: the normal
    covector is invariant, `K_TT` has two time tangents, and `K_AB` is screen
    transported, hence `DeltaK_PT=0` without a free sign;
  - this is a PT-transport raccord, not the standard outward-normal
    Israel cut-and-paste jump.
  - active writer:
    `write_p0_eft_janus_z2_pt67_regular_sigma_hk_inputs.py` writes
    `outputs/active_z2_sigma/pt67_regular_sigma_hk_inputs.json` with
    nondegenerate `h_ab`, unit normal, local `K_ab`, and `DeltaK_PT=0`.
  - Cartan/GHY writer:
    `write_p0_eft_janus_z2_pt67_cartan_ghy_deltaK_inputs.py` writes the
    standard `outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json` with
    `DeltaK_s=DeltaK_tau=0` from PT transport, no free orientation sign and no
    observational fit.
  - `CartanGHYComponentFromDeltaKInputsGate` now accepts the strict zero
    `DeltaK` branch without `background_scalars.json`, because
    `rho_CGHY=p_CGHY=0` before critical normalization.
  - Non-matter FLRW assembler status after PT67:
    Cartan/GHY exists, Holst/Nieh-Yan exists, and the nearest blocker is now
    only `counterterm_component`. The assembler reports
    `primary_blocker = counterterm_component` and
    `next_required = derive_and_write_counterterm_component`.
  - Counterterm is not closed by the PT67 update:
    `run_p0_eft_janus_z2_sigma_counterterm_chain.py` still blocks at
    `counterterm_trace_residual_inputs`, requiring active
    `R_h_trace/R_K_trace` or direct active surface density coefficients.
  - Dual-route counterterm race:
    `P0EFTJanusZ2SigmaCountertermMinimalBasisDualRouteDecisionGate` now checks
    both routes explicitly. Trace route is blocked by missing active
    `R_h/R_K` trace targets; direct surface-action route is blocked because
    current Janus inputs do not determine a unique local Sigma density. The
    only available expression is parametric
    `E_ct(R)=sqrt(q)*(6*c1*epsilon_Z2*R + 9*c2 + 6*c3)`, not promotable to a
    component without active coefficients or boundary conditions.
  - Holst/Palatini boundary bibliography update:
    Holst 1995, Corichi-Wilson-Ewing 2010, Corichi-RubalcavaGarcia-Vukasinac
    2016, Oliveri-Speziale 2019, and Corichi-Reyes 2015 support reconstructing
    the first-order boundary potential `theta(e,omega)` and checking the
    tetrad/metric boundary map. They do not by themselves determine the
    non-GHY counterterm traces. Next concrete target:
    project the Holst/Palatini boundary variation to Sigma/PT67 variables and
    extract or eliminate `R_h_trace/R_K_trace`.
  - Holst/Palatini theta projection now computed for PT67:
    `derive_p0_eft_janus_z2_sigma_holst_palatini_boundary_theta_pt67_projection.py`
    projects `theta_HP = P_IJ(e) wedge delta omega^IJ` onto the regular
    torsionless PT67 Sigma branch. Result:
    Palatini belongs to the already partitioned Cartan/GHY/junction channel,
    Holst is torsionless zero/exact-form only, and the non-GHY traces from this
    source are `R_h_trace=0`, `R_K_trace=0`. This narrows but does not close the
    counterterm, because independent Sigma surface densities and cross-action
    sources are still not excluded.
  - Boundary-Hamiltonian scalar route status:
    `H0_Z2Sigma`, `R_curv_Z2Sigma_m`, and `N_occ` are now classified as
    boundary/constraint targets, not independent densities. The FLRW
    proper-time lapse convention can be fixed (`N=1` on the restricted
    background), but it does not determine the dimensionful `H0` scale.
    Boundary-reference subtraction is now the active normalization route:
    set the quasilocal reference vacuum (`Minkowski/Milne`, depending on the
    active slicing) to zero energy. This fixes the additive zero and excludes a
    new independent Sigma density, but it still does not provide the physical
    boundary charge above the reference. Brown-York reduction is now formulaic:
    `E_BY = (1/kappa) integral_Sigma N sqrt(q) (k_ref-k_phys)`. Current
    frontier: the active S3 throat gives `k_ref-k_phys = 3(1-eps_Z2)/R_Sigma`
    and therefore `E_BY(eps=-1)=12*pi^2*R_Sigma^2/kappa_Z2Sigma`; the
    optimal-reference/isometric-embedding prescription fixes the subtraction
    and `k_ref` once the boundary metric is dimensionful. It does not by itself
    choose the absolute collar/throat scale. The remaining blocker is therefore
    still `R_Sigma` (or equivalently `ell_collar`). Once that is derived, map
    the charge to `H0_Z2Sigma` before writing
    `background_H0_normalization_inputs.json`.
  - Global topology scale audit:
    the active `S4/RP4 + resolved tunnel Sigma` topology fixes
    `R_Sigma/ell_collar = 1`, but is homothetic under
    `(R_Sigma, ell_collar) -> (L R_Sigma, L ell_collar)`. Therefore global
    topology alone cannot derive an absolute tunnel length. A dimensionful
    action/boundary/state input is required before `E_BY` can become numeric.
  - Cover-level scale audit:
    moving up to `JanusZ2CoverMasterAction` currently gives orientation,
    measure transport and symbolic `kappa_J`, but no dimensionful cover radius,
    length parameter, boundary charge value or descent map
    `R_Sigma = F[g_cover, constants, state]`. The homothety degeneracy therefore
    descends unchanged. The cover route can close `R_Sigma` only after the cover
    action is supplied with a real dimensionful datum or state-selection theorem.
  - `H0` closure route decision:
    Route B (Brown-York/quasilocal reference) remains the shortest route for
    fixing the boundary zero and `k_ref`. However the expression
    `12*pi^2/kappa*(R_Sigma^2-R_ref^2)` is a boundary energy difference, not
    directly a Hubble rate. Before writing `H0_Z2Sigma`, derive the
    Hamiltonian-boundary-charge to Friedmann-`H0` map and provide either an
    absolute `R_Sigma`, an action scale `ell_scale`, or a state/Noether charge.
  - Hamiltonian charge to Friedmann map:
    symbolic map is now fixed:
    `rho_H = Q_boundary_kg/V_eff_m3` or
    `rho_H = E_boundary_J/(c^2 V_eff_m3)`, then
    `H0^2 = (8*pi*G/3) rho_H - k c^2/R_curv^2`.
    Numeric closure still requires the charge convention/value, effective FLRW
    volume, curvature radius or flat limit, and absolute `R_Sigma`/state charge.
- [ ] Expand the residual coefficients:
  - derive `R_h^{ab} q_ab` and `R_K^{ab} q_ab` from the active Sigma
    counterterm density/action;
  - fix the `L_ct` integration constant from an active boundary condition;
  - materialize `counterterm_residual_scalar_contractions_inputs.json`;
  - only then derive `counterterm_lct_radial_profile.json` and
    `rsigma_E_counterterm.json`.

### Counterterm `L_ct` derivation objective

- [ ] Decide the active `L_ct(h,K,chi)` route from first principles, not by fit:
  - reject plain GHY/Brown-York duplication unless the term is shown not to
    double-count the active Cartan-GHY block;
  - reject pure Nieh-Yan as the full counterterm on the current torsionless
    branch because it only gives `R_chi partial_R chi = 0`;
  - test volume-solder/log-determinant as the identity-channel route only after
    the action bridge fixes the measure, lapse/slice factor and integration
    constant;
  - test transgression-style boundary action only if the two Janus sheet
    connections and boundary matching data are explicitly identified.
- [ ] Produce one of two concrete outcomes:
  - `counterterm_local_density_action_inputs.json` with explicit
    `L_ct_expression`, active provenance and no fitted coefficient; or
  - an obstruction report proving that the active Sigma counterterm cannot be
    reduced without additional physical boundary data.
- [ ] If the density is produced, run:
  - `derive_p0_eft_janus_z2_sigma_counterterm_residual_tensors_from_local_density_action.py`;
  - `derive_p0_eft_janus_z2_sigma_counterterm_residual_scalar_contractions.py`;
  - `derive_p0_eft_janus_z2_sigma_counterterm_lct_radial_profile_from_residual_contractions.py`;
  - `build_p0_eft_janus_z2_sigma_counterterm_radial_density_variation_input_writer_gate.py`;
  - `build_p0_eft_janus_z2_sigma_rsigma_counterterm_radial_term_from_density_variation_gate.py`.

## Priority 5 - Documentation locks

- [ ] Mark old mono-metric CMB hook failures as "CAMB-EFT tests", not Janus exclusion.
- [ ] Keep `full_cosmology_prediction_ready_no_fit = False` until Planck + BAO + growth pass under one derived bi-sector model.
- [x] Add a short architecture note explaining why Janus-orbifold may require a bi-sector Boltzmann backend.
