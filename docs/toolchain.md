# Janus Toolchain

Goal: move from verified sources to defensible predictions without mixing proof, implementation and observation.

## Layers

| Layer | Tool | Role | Current status |
|---|---|---|---|
| Source register | Markdown | Verified formulas and source claims | `docs/verified_formula_register.md` |
| Natural axioms | Markdown | Explicit assumptions | `formal/axioms/janus_axioms.md` |
| Canonical equations | LaTeX | Human-readable math | `formal/latex/janus_core_equations.tex` |
| Symbolic checks | SymPy | Algebraic sanity checks | `scripts/check_symbolic_formulas.py` |
| Formal proof | Lean 4 | Small logical kernels first | `formal/lean/JanusBasic.lean` |
| Numerical model | Python/NumPy | Predictions | `src/janus_lab/` |
| Statistical fit | SciPy/emcee/Cobaya | Data comparison | optional dependencies |
| Standard cosmology comparison | CLASS/CAMB/Cobaya | Later high-rigor comparison | not installed |

## Commands

Local Windows environment:

```powershell
.\.venv\Scripts\python.exe -m unittest discover tests
.\.venv\Scripts\python.exe scripts\build_p0_scross_candidate_triage_matrix.py
.\.venv\Scripts\python.exe scripts\build_p0_pt_lie_vjanus_ajanus_constraint_solver.py
.\.venv\Scripts\python.exe scripts\build_p0_ajanus_branch_selector_dynamics_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_ajanus_linear_residual_matching_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_ajanus_covariant_lift_obligation.py
.\.venv\Scripts\python.exe scripts\build_p0_covariant_q_field_candidate_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_relative_strain_q_regular_branch_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_relative_strain_dh_lgeom_vs_lorentz_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_sigma_dh_equivalence_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_sigma_source_traceability_gap_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_sigma_trace_only_no_go_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_projector_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_projector_variation_dependency_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_source_candidate_matrix.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_irrep_source_requirements_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_action_operator_requirements_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_closure_obligation_matrix.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_scalar_vector_no_go_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_variational_source_template_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_variational_action_basis_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_action_basis_el_variation_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_action_measure_variation_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_frechet_log_adjoint_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_qtf_to_h_chain_rule_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_quadratic_qtf_h_el_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_linear_qtf_xtf_h_el_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_same_l_spin_connection_transport_identity_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_same_l_bridge_induces_m_k_qcross_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_janus_coupled_stress_stf_transport_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_xtf_source_provenance_variation_contract.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_action_basis_acceptance_filter.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_linear_coupling_rank_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_derivative_branch_stability_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_linear_xtf_provenance_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_same_bridge_dependency_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_source_action_provenance_chain_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_derivation_attack_plan.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_anisotropic_stress_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_weyl_shear_source_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_vlasov_quadrupole_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_relative_strain_action_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_bf_gl_phi_sigma_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_tracefree_h_isotropy_no_go_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_h_strain_action_variation_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_h_strain_ghost_symbolic_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_nonmetricity_integrability_curl_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_nonmetricity_curl_numeric_probe.py
.\.venv\Scripts\python.exe scripts\build_p0_nonmetricity_mirror_inverse_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_phi_sigma_source_action_decision_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_nonmetricity_source_acceptance_criteria.py
.\.venv\Scripts\python.exe scripts\build_p0_nonmetricity_rank_reduction_ledger.py
.\.venv\Scripts\python.exe scripts\build_p0_relative_metric_nonmetricity_sigma_dh_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_stueckelberg_sigma_dh_variation_rank_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_cartan_bf_gl_strain_selector_gate.py
.\.venv\Scripts\python.exe scripts\build_p0_sigma_source_selector_attack_matrix.py
.\.venv\Scripts\python.exe scripts\build_p0_relative_strain_q_derivative_omega_gate.py
```

```powershell
python -m pip install -e .
python scripts\run_formal_checks.py
python scripts\verify_newtonian_source_anchors.py
python scripts\simulate_two_sector_pairs.py
python scripts\simulate_two_sector_poisson_grid.py
python scripts\simulate_two_sector_poisson_grid_3d.py
python scripts\simulate_two_sector_particle_mesh.py
python scripts\simulate_two_sector_particle_mesh_3d.py
python scripts\benchmark_vectorized_pm_3d.py
python scripts\benchmark_vectorized_pm_3d_progressive.py
python scripts\run_vectorized_pm_3d_short_stability.py
python scripts\diagnose_particle_mesh_resolution.py
python scripts\simulate_two_sector_segregation.py
python scripts\analyze_segregation_fields.py
python scripts\diagnose_segregation_robustness.py
python scripts\compare_segregation_controls.py
python scripts\diagnose_control_robustness.py
python scripts\simulate_cosmological_pm_prototype.py
python scripts\simulate_cosmological_pm_3d_prototype.py
python scripts\diagnose_cosmological_pm_robustness.py
python scripts\generate_gaussian_initial_conditions.py
python scripts\simulate_cosmological_pm_gaussian_ic.py
python scripts\generate_gaussian_initial_conditions_3d.py
python scripts\simulate_cosmological_pm_3d_gaussian_ic.py
python scripts\diagnose_gaussian_ic_seed_robustness.py
python scripts\analyze_cosmological_pm_power_observables.py
python scripts\analyze_cosmological_pm_3d_power_observables.py
python scripts\diagnose_cosmological_pm_3d_power_robustness.py
python scripts\calibrate_physical_pm_box.py
python scripts\analyze_cosmological_pm_3d_physical_power.py
python scripts\diagnose_sigma8_resolution_requirements.py
python scripts\generate_sigma8_normalized_ic_3d.py
python scripts\generate_lognormal_sigma8_ic_3d.py
python scripts\diagnose_bounded_anticorrelated_sigma8_ic_3d.py
python scripts\diagnose_lensing_source_map.py
python scripts\diagnose_lensing_sigma8_observable.py
python scripts\diagnose_weak_lensing_projection.py
python scripts\diagnose_janus_tomographic_lensing_kernel.py
python scripts\diagnose_janus_shear_proxy.py
python scripts\diagnose_janus_source_distribution_lensing.py
python scripts\diagnose_janus_absolute_convergence.py
python scripts\build_lensing_normalization_audit.py
python scripts\build_sigma8_observable_map_report.py
python scripts\infer_janus_bao_ruler.py
python scripts\build_bao_observable_map_report.py
python scripts\score_bao_c2_gauge.py
python scripts\score_bao_c4_observable.py
python scripts\score_bao_c5_redshift.py
python scripts\score_bao_c6_sound_horizon.py
python scripts\score_bao_c7_anisotropic_linear_ruler.py
python scripts\score_bao_c8_source_gauge_no_fit.py
python -m unittest discover -s tests
```

Optional fitting tools:

```powershell
python -m pip install -e .[fit]
```

Optional cosmology stack:

```powershell
python -m pip install -e .[cosmo]
```

Lean is separate. Install it with `elan`, then run:

```powershell
lean formal\lean\JanusBasic.lean
```

## Rule

Do not use Lean to prove observational truth. Use it to prove that stated assumptions imply stated consequences. Observational validation remains Python/data/statistics.
