from __future__ import annotations

from pathlib import Path
import json

from janus_lab.particle_mesh_3d_vectorized import estimate_vectorized_pm_memory_bytes


PREDICTION_GATE_PATH = Path("outputs/reports/prediction_claim_gate.json")
SCAFFOLDS_PATH = Path("outputs/reports/remaining_scaffolds_roadmap.json")
PM_CONVERGENCE_PATH = Path("outputs/reports/pm_convergence_family_comparison.json")
OBSERVABLE_CHAIN_PATH = Path("outputs/reports/observable_chain_consistency_audit.json")
SURVEY_INTERFACE_PATH = Path("outputs/reports/survey_likelihood_interface.json")
PARTIAL_ARTIFACT_PATHS = [
    Path("outputs/reports/bianchi_lorentz_boost_transport_branch.json"),
    Path("outputs/reports/bianchi_l_map_source_equations_target.json"),
    Path("outputs/reports/bianchi_lorentz_residual_reduction.json"),
    Path("outputs/reports/bianchi_l_derivative_obstruction.json"),
    Path("outputs/reports/bianchi_transported_continuity_target.json"),
    Path("outputs/reports/bianchi_connection_force_cancellation_target.json"),
    Path("outputs/reports/bianchi_conditional_closure_theorem.json"),
    Path("outputs/reports/bianchi_transported_geodesic_force_target.json"),
    Path("outputs/reports/bianchi_transport_continuity_force_target.json"),
    Path("outputs/reports/p0_l_k_qcross_consistency_target.json"),
    Path("outputs/reports/p0_janus_transport_residual_derivation.json"),
    Path("outputs/reports/p0_interaction_tensor_research_program.json"),
    Path("outputs/reports/p0_l_transport_candidate_geometry.json"),
    Path("outputs/reports/p0_source_transport_f_equations.json"),
    Path("outputs/reports/p0_f_decomposition_and_gauge.json"),
    Path("outputs/reports/p0_fermi_walker_transport_branch.json"),
    Path("outputs/reports/p0_receiver_geodesic_transport_derivation.json"),
    Path("outputs/reports/p0_perfect_fluid_transport_constraints.json"),
    Path("outputs/reports/p0_anisotropic_stress_orientation_constraints.json"),
    Path("outputs/reports/p0_branch_decision_matrix.json"),
    Path("outputs/reports/p0_k_interaction_tensor_candidate_families.json"),
    Path("outputs/reports/p0_bianchi_closure_candidate_criteria.json"),
    Path("outputs/reports/p0_density_measure_closure_condition.json"),
    Path("outputs/reports/p0_source_measure_convention_matrix.json"),
    Path("outputs/reports/p0_source_measure_selection_rules.json"),
    Path("outputs/reports/p0_source_measure_residual_substitution.json"),
    Path("outputs/reports/p0_residual_zero_condition_matrix.json"),
    Path("outputs/reports/p0_dl_dlogb_identity_targets.json"),
    Path("outputs/reports/p0_dl_lorentz_generator_obstruction.json"),
    Path("outputs/reports/p0_dlogb_4volume_obstruction.json"),
    Path("outputs/reports/p0_m15_source_identity_implications.json"),
    Path("outputs/reports/p0_source_gap_scan_results.json"),
    Path("outputs/reports/p0_minimal_axiom_transport_solution.json"),
    Path("outputs/reports/p0_m30_zero_divergence_pde_derivation.json"),
    Path("outputs/reports/p0_zero_divergence_solver_plan.json"),
    Path("outputs/reports/p0_flrw_zero_divergence_toy_solution.json"),
    Path("outputs/reports/p0_noncomoving_dust_pde_constraints.json"),
    Path("outputs/reports/p0_omega_transverse_gauge_audit.json"),
    Path("outputs/reports/p0_pi_eigenframe_gauge_fix_branch.json"),
    Path("outputs/reports/p0_l_boundary_initial_condition_branch.json"),
    Path("outputs/reports/p0_gauge_lifting_decision_matrix.json"),
    Path("outputs/reports/p0_gauge_source_scan_results.json"),
    Path("outputs/reports/p0_flat_omega_connection_branch.json"),
    Path("outputs/reports/p0_pure_gauge_solder_connection_branch.json"),
    Path("outputs/reports/p0_pure_gauge_pde_consistency_check.json"),
    Path("outputs/reports/p0_relative_holonomy_branch.json"),
    Path("outputs/reports/p0_flat_vs_holonomy_decision.json"),
    Path("outputs/reports/p0_lorentz_polar_projection_regular_branch.json"),
    Path("outputs/reports/p0_relative_strain_q_regular_branch_gate.json"),
    Path("outputs/reports/p0_relative_strain_dh_lgeom_vs_lorentz_gate.json"),
    Path("outputs/reports/p0_sigma_dh_equivalence_gate.json"),
    Path("outputs/reports/p0_sigma_source_traceability_gap_gate.json"),
    Path("outputs/reports/p0_sigma_trace_only_no_go_gate.json"),
    Path("outputs/reports/p0_tracefree_h_projector_gate.json"),
    Path("outputs/reports/p0_tracefree_h_projector_variation_dependency_gate.json"),
    Path("outputs/reports/p0_tracefree_h_source_candidate_matrix.json"),
    Path("outputs/reports/p0_tracefree_h_irrep_source_requirements_gate.json"),
    Path("outputs/reports/p0_tracefree_h_action_operator_requirements_gate.json"),
    Path("outputs/reports/p0_tracefree_h_closure_obligation_matrix.json"),
    Path("outputs/reports/p0_tracefree_h_scalar_vector_no_go_gate.json"),
    Path("outputs/reports/p0_tracefree_h_variational_source_template_gate.json"),
    Path("outputs/reports/p0_tracefree_h_variational_action_basis_gate.json"),
    Path("outputs/reports/p0_tracefree_h_action_basis_el_variation_gate.json"),
    Path("outputs/reports/p0_tracefree_h_action_measure_variation_gate.json"),
    Path("outputs/reports/p0_tracefree_h_frechet_log_adjoint_gate.json"),
    Path("outputs/reports/p0_tracefree_h_qtf_to_h_chain_rule_gate.json"),
    Path("outputs/reports/p0_tracefree_h_quadratic_qtf_h_el_gate.json"),
    Path("outputs/reports/p0_tracefree_h_linear_qtf_xtf_h_el_gate.json"),
    Path("outputs/reports/p0_tracefree_h_janus_coupled_stress_stf_transport_gate.json"),
    Path("outputs/reports/p0_tracefree_h_xtf_source_provenance_variation_contract.json"),
    Path("outputs/reports/p0_tracefree_h_action_basis_acceptance_filter.json"),
    Path("outputs/reports/p0_tracefree_h_linear_coupling_rank_gate.json"),
    Path("outputs/reports/p0_tracefree_h_derivative_branch_stability_gate.json"),
    Path("outputs/reports/p0_tracefree_h_linear_xtf_provenance_gate.json"),
    Path("outputs/reports/p0_tracefree_h_same_bridge_dependency_gate.json"),
    Path("outputs/reports/p0_tracefree_h_source_action_provenance_chain_gate.json"),
    Path("outputs/reports/p0_tracefree_h_derivation_attack_plan.json"),
    Path("outputs/reports/p0_tracefree_h_anisotropic_stress_gate.json"),
    Path("outputs/reports/p0_tracefree_h_weyl_shear_source_gate.json"),
    Path("outputs/reports/p0_tracefree_h_vlasov_quadrupole_gate.json"),
    Path("outputs/reports/p0_tracefree_h_relative_strain_action_gate.json"),
    Path("outputs/reports/p0_tracefree_h_bf_gl_phi_sigma_gate.json"),
    Path("outputs/reports/p0_tracefree_h_isotropy_no_go_gate.json"),
    Path("outputs/reports/p0_h_strain_action_variation_gate.json"),
    Path("outputs/reports/p0_h_strain_ghost_symbolic_gate.json"),
    Path("outputs/reports/p0_nonmetricity_integrability_curl_gate.json"),
    Path("outputs/reports/p0_nonmetricity_curl_numeric_probe.json"),
    Path("outputs/reports/p0_nonmetricity_mirror_inverse_gate.json"),
    Path("outputs/reports/p0_phi_sigma_source_action_decision_gate.json"),
    Path("outputs/reports/p0_nonmetricity_source_acceptance_criteria.json"),
    Path("outputs/reports/p0_nonmetricity_rank_reduction_ledger.json"),
    Path("outputs/reports/p0_relative_metric_nonmetricity_sigma_dh_gate.json"),
    Path("outputs/reports/p0_stueckelberg_sigma_dh_variation_rank_gate.json"),
    Path("outputs/reports/p0_cartan_bf_gl_strain_selector_gate.json"),
    Path("outputs/reports/p0_sigma_source_selector_attack_matrix.json"),
    Path("outputs/reports/p0_relative_strain_q_derivative_omega_gate.json"),
    Path("outputs/reports/p0_holonomy_path_rule_branch.json"),
    Path("outputs/reports/p0_polar_projection_derivative_obstruction.json"),
    Path("outputs/reports/p0_holonomy_loop_consistency_criteria.json"),
    Path("outputs/reports/p0_transport_branch_closure_obligations.json"),
    Path("outputs/reports/p0_solution_route_selection.json"),
    Path("outputs/reports/p0_variational_closure_route.json"),
    Path("outputs/reports/p0_integrability_closure_route.json"),
    Path("outputs/reports/p0_source_derived_route_attempt.json"),
    Path("outputs/reports/p0_auxiliary_l_action_attempt.json"),
    Path("outputs/reports/p0_innovative_axiom_acceptance_gate.json"),
    Path("outputs/reports/p0_stueckelberg_two_diffeo_route.json"),
    Path("outputs/reports/p0_stueckelberg_conditional_closure_theorem.json"),
    Path("outputs/reports/p0_stueckelberg_explicit_action_test.json"),
    Path("outputs/reports/p0_stueckelberg_minimal_phi_dust_test.json"),
    Path("outputs/reports/p0_stueckelberg_mirror_phi_constraints.json"),
    Path("outputs/reports/p0_stueckelberg_zero_param_progression.json"),
    Path("outputs/reports/p0_stueckelberg_zero_param_dust_compatibility.json"),
    Path("outputs/reports/p0_stueckelberg_zero_param_residual_substitution.json"),
    Path("outputs/reports/p0_stueckelberg_dphi_density_cancellation.json"),
    Path("outputs/reports/p0_stueckelberg_dl_velocity_cancellation.json"),
    Path("outputs/reports/p0_stueckelberg_dlogb_volume_cancellation.json"),
    Path("outputs/reports/p0_stueckelberg_remaining_connection_gate.json"),
    Path("outputs/reports/p0_stueckelberg_connection_difference_cancellation.json"),
    Path("outputs/reports/p0_stueckelberg_map_equation_connection_compatibility.json"),
    Path("outputs/reports/p0_stueckelberg_dust_congruence_escape_route.json"),
    Path("outputs/reports/p0_stueckelberg_map_constraint_counting.json"),
    Path("outputs/reports/p0_stueckelberg_map_integrability_curl_conditions.json"),
    Path("outputs/reports/p0_stueckelberg_isometry_branch_no_go.json"),
    Path("outputs/reports/p0_stueckelberg_weak_congruence_map_equation.json"),
    Path("outputs/reports/p0_stueckelberg_weak_congruence_variational_origin.json"),
    Path("outputs/reports/p0_stueckelberg_dust_current_multiplier_identification.json"),
    Path("outputs/reports/p0_stueckelberg_transverse_source_requirement.json"),
    Path("outputs/reports/p0_stueckelberg_projected_dust_variation_identity.json"),
    Path("outputs/reports/p0_stueckelberg_projected_perfect_fluid_extension.json"),
    Path("outputs/reports/p0_stueckelberg_phi_l_convention_lock.json"),
    Path("outputs/reports/p0_stueckelberg_dust_branch_conditional_closure_gate.json"),
    Path("outputs/reports/p0_stueckelberg_dust_image_curl_reduction.json"),
    Path("outputs/reports/p0_stueckelberg_transverse_label_caustic_gate.json"),
    Path("outputs/reports/p0_stueckelberg_multistream_extension_gate.json"),
    Path("outputs/reports/p0_stueckelberg_sheet_sum_dust_model.json"),
    Path("outputs/reports/p0_stueckelberg_sheet_creation_conservation_gate.json"),
    Path("outputs/reports/p0_stueckelberg_kinetic_moment_sheet_limit.json"),
    Path("outputs/reports/p0_stueckelberg_sheet_optical_no_fit_gate.json"),
    Path("outputs/reports/p0_stueckelberg_sheet_diagnostic_execution_gate.json"),
    Path("outputs/reports/p0_stueckelberg_kinetic_transport_candidate.json"),
    Path("outputs/reports/p0_stueckelberg_qcross_kinetic_projection_candidate.json"),
    Path("outputs/reports/p0_stueckelberg_rkin_pushforward_derivation.json"),
    Path("outputs/reports/p0_stueckelberg_popt_acceptance_criteria.json"),
    Path("outputs/reports/p0_stueckelberg_popt_null_tetrad_candidate.json"),
    Path("outputs/reports/p0_stueckelberg_rkin_commutator_closure_gate.json"),
    Path("outputs/reports/p0_stueckelberg_sachs_optical_source_gate.json"),
    Path("outputs/reports/p0_stueckelberg_popt_reduced_sachs_candidate.json"),
    Path("outputs/reports/p0_stueckelberg_janus_ricci_sign_substitution_gate.json"),
    Path("outputs/reports/p0_stueckelberg_lensing_observable_chain_gate.json"),
    Path("outputs/reports/p0_stueckelberg_scross_source_anchor.json"),
    Path("outputs/reports/p0_stueckelberg_shear_distance_gauge_closure_gate.json"),
    Path("outputs/reports/p0_stueckelberg_weyl_shear_diagnostic_gate.json"),
    Path("outputs/reports/p0_stueckelberg_observer_source_gauge_contract.json"),
    Path("outputs/reports/p0_stueckelberg_perturbed_metric_weyl_solver_target.json"),
    Path("outputs/reports/p0_stueckelberg_gauge_contract_instantiation_target.json"),
    Path("outputs/reports/p0_stueckelberg_weak_field_weyl_operator.json"),
    Path("outputs/reports/p0_stueckelberg_weak_field_weyl_source_chain.json"),
    Path("outputs/reports/p0_stueckelberg_metric_potential_closure_contract.json"),
    Path("outputs/reports/p0_stueckelberg_linearized_field_equation_branch.json"),
    Path("outputs/reports/p0_stueckelberg_gauge_slip_branch.json"),
    Path("outputs/reports/p0_stueckelberg_source_identity_branch.json"),
    Path("outputs/reports/p0_stueckelberg_metric_potential_promotion_gate.json"),
    Path("outputs/reports/p0_stueckelberg_comoving_scalar_metric_closure_candidate.json"),
    Path("outputs/reports/p0_stueckelberg_noncomoving_source_identity_target.json"),
    Path("outputs/reports/p0_stueckelberg_beta_field_provenance_gate.json"),
    Path("outputs/reports/p0_stueckelberg_beta_vec_u_transport_target.json"),
    Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_closure_requirements.json"),
    Path("outputs/reports/p0_source_derived_beta_reconstruction_target.json"),
    Path("outputs/reports/janus_linear_beta_vec_closure_gate.json"),
    Path("outputs/reports/janus_linear_source_operator_closure_target.json"),
    Path("outputs/reports/janus_linear_theta_beta_derivation.json"),
    Path("outputs/reports/janus_linear_theta_mode_reduction_derivation.json"),
    Path("outputs/reports/p0_noncomoving_momentum_t0i_closure_target.json"),
    Path("outputs/reports/p0_stueckelberg_noncomoving_pressure_pi_residual_substitution_gate.json"),
    Path("outputs/reports/p0_same_l_dl_residual_closure_ledger.json"),
    Path("outputs/reports/p0_same_phi_l_cuu_bridge.json"),
    Path("outputs/reports/p0_dynamic_phi_l_selection_mirror_closure.json"),
    Path("outputs/reports/p0_janus_phi_l_xi_map_equation_gate.json"),
    Path("outputs/reports/p0_janus_phi_l_ephi_el_variational_origin_gate.json"),
    Path("outputs/reports/p0_janus_exact_source_term_closure_attack.json"),
    Path("outputs/reports/p0_janus_soldered_l_substitution_residual_gate.json"),
    Path("outputs/reports/p0_janus_metric_pullback_compatibility_gate.json"),
    Path("outputs/reports/p0_janus_metric_pullback_phi_selector_gate.json"),
    Path("outputs/reports/p0_janus_source_isometry_selection_no_go.json"),
    Path("outputs/reports/p0_janus_weak_congruence_selector_derivation_gate.json"),
    Path("outputs/reports/p0_janus_active_cross_action_acceptance_gate.json"),
    Path("outputs/reports/p0_janus_weak_selector_action_origin_audit.json"),
    Path("outputs/reports/p0_janus_pulled_dust_action_weak_congruence_proof.json"),
    Path("outputs/reports/p0_janus_next_work_organization_review.json"),
    Path("outputs/reports/p0_no_axiom_route_exhaustion_program.json"),
    Path("outputs/reports/p0_route_a_integrability_nullspace_audit.json"),
    Path("outputs/reports/p0_stueckelberg_sheetwise_kinetic_transport_gate.json"),
    Path("outputs/reports/p0_route_c_geometric_exotic_completion_gate.json"),
    Path("outputs/reports/p0_route_c_bf_holonomy_priority_attack.json"),
    Path("outputs/reports/p0_route_c_phi_r_curvature_identity_gate.json"),
    Path("outputs/reports/p0_route_c_phi_r_relative_curvature_selector_probe.json"),
    Path("outputs/reports/p0_route_c_small_loop_holonomy_numeric_probe.json"),
    Path("outputs/reports/p0_route_c_path_rule_selector_matrix.json"),
    Path("outputs/reports/p0_route_c_two_path_nonunique_l_probe.json"),
    Path("outputs/reports/p0_route_c_janus_path_rule_source_derivation_gate.json"),
    Path("outputs/reports/p0_route_c_boundary_gauge_unique_l_obstruction.json"),
    Path("outputs/reports/p0_route_c_no_path_rule_underselection_theorem.json"),
    Path("outputs/reports/p0_route_c_indirect_path_rule_source_audit.json"),
    Path("outputs/reports/p0_route_c_action_noether_path_rule_derivation_attempt.json"),
    Path("outputs/reports/p0_route_c_pt_geometry_path_rule_audit.json"),
    Path("outputs/reports/p0_route_c_pt_selector_derivation_attempt.json"),
    Path("outputs/reports/p0_route_c_pt_only_no_selector_certificate.json"),
    Path("outputs/reports/p0_route_c_pt_fixed_path_extension_candidate_gate.json"),
    Path("outputs/reports/p0_route_c_ordered_path_action_source_derivation_gate.json"),
    Path("outputs/reports/p0_route_c_minimal_spath_extension_axiom_gate.json"),
    Path("outputs/reports/p0_route_c_spath_euler_lagrange_equations.json"),
    Path("outputs/reports/p0_route_c_spath_lorentz_tetrad_variation_gate.json"),
    Path("outputs/reports/p0_route_c_spath_same_l_substitution_gate.json"),
    Path("outputs/reports/p0_route_c_spath_stability_screen.json"),
    Path("outputs/reports/p0_route_c_spath_scalar_density_completion_gate.json"),
    Path("outputs/reports/p0_route_c_spath_cj_vj_invariant_filter.json"),
    Path("outputs/reports/p0_route_c_spath_cj_vj_coefficient_underselection_gate.json"),
    Path("outputs/reports/p0_route_c_spath_cj_vj_filter_rank_no_go.json"),
    Path("outputs/reports/p0_route_c_spath_cj_vj_nonlinear_local_no_go.json"),
    Path("outputs/reports/p0_route_c_spath_constraint_equation_classifier.json"),
    Path("outputs/reports/p0_orbifold_pt_soldering_candidate.json"),
    Path("outputs/reports/p0_orbifold_pt_action_variation_gate.json"),
    Path("outputs/reports/p0_orbifold_pt_source_current_gate.json"),
    Path("outputs/reports/p0_orbifold_pt_defect_matching_law_gate.json"),
    Path("outputs/reports/p0_orbifold_pt_bdefect_action_filter.json"),
    Path("outputs/reports/p0_orbifold_pt_topological_defect_branch_gate.json"),
    Path("outputs/reports/p0_orbifold_pt_ktop_quantization_gate.json"),
    Path("outputs/reports/p0_route_c_spath_metric_stress_variation_gate.json"),
    Path("outputs/reports/p0_route_c_spath_bianchi_noether_gate.json"),
    Path("outputs/reports/p0_local_low_derivative_scalar_tensor_no_go_expansion.json"),
    Path("outputs/reports/p0_route_d_no_go_structural_matrix.json"),
    Path("outputs/reports/p0_route_d_tensor_derivative_admissibility_filter.json"),
    Path("outputs/reports/p0_route_d_derivative_curvature_nullspace_gate.json"),
    Path("outputs/reports/p0_route_d_source_free_pde_nullspace_probe.json"),
    Path("outputs/reports/p0_route_d_source_free_boundary_no_go_argument.json"),
    Path("outputs/reports/p0_route_d_local_pde_no_selector_certificate.json"),
    Path("outputs/reports/p0_route_d_source_derived_stf_operator_escape_gate.json"),
    Path("outputs/reports/p0_route_d_stf_operator_construction_obstruction.json"),
    Path("outputs/reports/p0_route_d_stf_no_go_closure_attempt.json"),
    Path("outputs/reports/p0_zero_axiom_closure_decision_gate.json"),
    Path("outputs/reports/p0_minimal_nonrustine_extension_contract.json"),
    Path("outputs/reports/p0_remaining_research_priority_queue.json"),
    Path("outputs/reports/p0_phi_scouple_source_or_axiom_decision.json"),
    Path("outputs/reports/p0_phi_scouple_anti_rustine_gate.json"),
    Path("outputs/reports/p0_phi_scouple_forced_selection_search.json"),
    Path("outputs/reports/p0_global_review_outside_box_routes.json"),
    Path("outputs/reports/p0_integrability_first_phi_l_selection.json"),
    Path("outputs/reports/p0_integrability_first_equation_system.json"),
    Path("outputs/reports/p0_integrability_regular_patch_toy_solver.json"),
    Path("outputs/reports/p0_local_phi_scouple_no_go_target.json"),
    Path("outputs/reports/p0_local_phi_scouple_symbolic_restricted_audit.json"),
    Path("outputs/reports/p0_split_noether_calculable_target.json"),
    Path("outputs/reports/p0_split_noether_linear_phi_candidate.json"),
    Path("outputs/reports/p0_linear_imatter_tensor_contract.json"),
    Path("outputs/reports/p0_linear_imatter_metric_variation.json"),
    Path("outputs/reports/p0_linear_imatter_stress_response_target.json"),
    Path("outputs/reports/p0_matter_action_stress_response_target.json"),
    Path("outputs/reports/p0_dust_metric_stress_response_target.json"),
    Path("outputs/reports/p0_dust_fixed_current_density_response.json"),
    Path("outputs/reports/p0_dust_densitized_current_density_response.json"),
    Path("outputs/reports/p0_dust_pullback_density_response_bridge.json"),
    Path("outputs/reports/p0_source_pullback_metric_response_target.json"),
    Path("outputs/reports/p0_dust_fixed_pullback_delta_t_branch.json"),
    Path("outputs/reports/p0_linear_imatter_conditional_dust_k_variation.json"),
    Path("outputs/reports/p0_pulled_m_metric_response_target.json"),
    Path("outputs/reports/p0_l_metric_response_law_target.json"),
    Path("outputs/reports/p0_pulled_m_symmetric_l_substitution.json"),
    Path("outputs/reports/p0_omega_residual_closure_gate.json"),
    Path("outputs/reports/p0_omega_dust_rank_one_condition.json"),
    Path("outputs/reports/p0_omega_k_qcross_consistency_gate.json"),
    Path("outputs/reports/p0_omega_closure_routes_gate.json"),
    Path("outputs/reports/p0_omega_u_zero_source_derivation_target.json"),
    Path("outputs/reports/p0_omega_source_law_trial_gate.json"),
    Path("outputs/reports/p0_fermi_walker_omega_u_zero_trial.json"),
    Path("outputs/reports/p0_source_congruence_omega_gate.json"),
    Path("outputs/reports/p0_omega_source_or_axiom_decision.json"),
    Path("outputs/reports/p0_janus_source_omega_traceability_audit.json"),
    Path("outputs/reports/p0_transport_axiom_acceptance_gate.json"),
    Path("outputs/reports/p0_transport_axiom_candidate_statement.json"),
    Path("outputs/reports/p0_omega_next_decision_matrix.json"),
    Path("outputs/reports/p0_external_janus_omega_source_search_gate.json"),
    Path("outputs/reports/p0_external_janus_omega_source_search_results.json"),
    Path("outputs/reports/p0_external_source_search_omega_transport_audit.json"),
    Path("outputs/reports/p0_external_source_search_scouple_phi_audit.json"),
    Path("outputs/reports/p0_du_l_omega_dynamic_derivation_attempt.json"),
    Path("outputs/reports/p0_omega_source_no_go_axiom_boundary.json"),
    Path("outputs/reports/p0_dlogb4vol_measure_law_derivation_attempt.json"),
    Path("outputs/reports/p0_pressure_pi_omega_extension_blocker.json"),
    Path("outputs/reports/p0_janus_equations_to_l_omega_law_attempt.json"),
    Path("outputs/reports/p0_janus_equations_to_dlogb4vol_closure_attempt.json"),
    Path("outputs/reports/p0_bianchi_minimal_joint_dl_dlogb_solution.json"),
    Path("outputs/reports/p0_bianchi_minimal_integrability_mirror_gate.json"),
    Path("outputs/reports/p0_bianchi_minimal_full_connection_lift_system.json"),
    Path("outputs/reports/p0_bianchi_minimal_mirror_inverse_attempt.json"),
    Path("outputs/reports/p0_bianchi_minimal_curvature_integrability_system.json"),
    Path("outputs/reports/p0_flrw_relative_curvature_rows_target.json"),
    Path("outputs/reports/p0_weakfield_relative_curvature_rows_target.json"),
    Path("outputs/reports/p0_weakfield_tetrad_connection_target.json"),
    Path("outputs/reports/p0_janus_source_tetrad_requirements.json"),
    Path("outputs/reports/p0_janus_weakfield_metric_tetrad_bridge.json"),
    Path("outputs/reports/p0_janus_weakfield_source_potential_system.json"),
    Path("outputs/reports/p0_janus_weakfield_delta_s00_source_expansion_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_delta_s00_measure_convention_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_phi_l_map_density_response_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_delta_s00_density_transport_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_delta_phi_psi_source_chain_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_phi_psi_qdet_source_closure_attempt.json"),
    Path("outputs/reports/p0_janus_weakfield_dust_slip_poisson_target.json"),
    Path("outputs/reports/p0_janus_weakfield_dust_slip_fourier_solver_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_zero_mode_background_gauge_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_dust_slip_green_kernel_target.json"),
    Path("outputs/reports/p0_janus_source_selected_branch_matrix.json"),
    Path("outputs/reports/p0_janus_weakfield_lgeom_lorentz_no_go_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_lorentz_projection_derivation.json"),
    Path("outputs/reports/p0_janus_weakfield_shift_boost_t0i_derivation.json"),
    Path("outputs/reports/p0_janus_weakfield_g0i_shift_operator_derivation.json"),
    Path("outputs/reports/p0_janus_pressure_pi0i_transport_gate.json"),
    Path("outputs/reports/p0_janus_pressure_pi0i_transport_derivation.json"),
    Path("outputs/reports/p0_janus_g0i_dust_beta_inversion_target.json"),
    Path("outputs/reports/p0_janus_matter_eos_pi_branch_decision.json"),
    Path("outputs/reports/p0_janus_eos_pi_source_audit.json"),
    Path("outputs/reports/p0_janus_conditional_dust_branch_contract.json"),
    Path("outputs/reports/p0_janus_kinetic_moment_eos_pi_closure_target.json"),
    Path("outputs/reports/p0_janus_kinetic_moment_hierarchy_equations.json"),
    Path("outputs/reports/p0_janus_kinetic_closure_routes_decision.json"),
    Path("outputs/reports/p0_janus_full_vlasov_moment_closure_contract.json"),
    Path("outputs/reports/p0_janus_pi_zero_preservation_gate.json"),
    Path("outputs/reports/p0_janus_vlasov_geodesic_force_target.json"),
    Path("outputs/reports/p0_janus_eos_prho_no_go_vlasov_gate.json"),
    Path("outputs/reports/p0_janus_metric_tetrad_source_branch_gate.json"),
    Path("outputs/reports/p0_janus_weakfield_metric_force_probe.json"),
    Path("outputs/reports/p0_janus_same_l_transport_stack_gate.json"),
    Path("outputs/reports/p0_same_l_spin_connection_transport_identity_gate.json"),
    Path("outputs/reports/p0_same_l_bridge_induces_m_k_qcross_gate.json"),
    Path("outputs/reports/p0_janus_phase_space_b4vol_measure_gate.json"),
    Path("outputs/reports/p0_janus_same_l_1p1_lorentz_probe.json"),
    Path("outputs/reports/p0_janus_lgeom_tetrad_map_residual_probe.json"),
    Path("outputs/reports/p0_janus_lgeom_dl_lie_residual_probe.json"),
    Path("outputs/reports/p0_janus_phase_space_measure_probe.json"),
    Path("outputs/reports/p0_janus_weakfield_b4vol_product_rule_probe.json"),
    Path("outputs/reports/p0_shared_phi_j_source_selection_gate.json"),
    Path("outputs/reports/p0_source_derived_same_l_dl_residual_closure_target.json"),
    Path("outputs/reports/p0_dlogb4vol_source_slice_lapse_obligation_ledger.json"),
    Path("outputs/reports/p0_dlogb4vol_jacobian_lapse_slice_identity_target.json"),
    Path("outputs/reports/p0_falpha_source_law_obligation_ledger.json"),
    Path("outputs/reports/p0_falpha_from_jacobian_tetrad_identity_target.json"),
    Path("outputs/reports/p0_projected_cuu_action_pullback_bridge_ledger.json"),
    Path("outputs/reports/p0_cuu_inverse_map_integrability_target.json"),
    Path("outputs/reports/p0_cuu_jacobian_curl_numeric_probe.json"),
    Path("outputs/reports/p0_janus_effective_vlasov_solver_gate.json"),
    Path("outputs/reports/p0_janus_effective_vlasov_solver_probe.json"),
    Path("outputs/reports/p0_janus_two_sector_vlasov_poisson_probe.json"),
    Path("outputs/reports/p0_janus_metric_force_vlasov_step_probe.json"),
    Path("outputs/reports/p0_janus_two_sector_metric_force_vlasov_probe.json"),
    Path("outputs/reports/p0_janus_diagnostic_closure_dashboard.json"),
    Path("outputs/reports/p0_janus_source_residual_closure_obligation_matrix.json"),
    Path("outputs/reports/p0_bianchi_minimal_curvature_numeric_probe.json"),
    Path("outputs/reports/p0_curvature_integrability_sparse_pde_probe.json"),
    Path("outputs/reports/p0_weakfield_curvature_injection_probe.json"),
    Path("outputs/reports/p0_weakfield_tetrad_pipeline_probe.json"),
    Path("outputs/reports/p0_bianchi_minimal_same_l_qcross_gate.json"),
    Path("outputs/reports/p0_mirror_inverse_numeric_residual_probe.json"),
    Path("outputs/reports/p0_same_l_qcross_numeric_contraction_probe.json"),
    Path("outputs/reports/p0_omega_projection_annihilation_gate.json"),
    Path("outputs/reports/p0_linear_imatter_l_variation.json"),
    Path("outputs/reports/p0_linear_imatter_lorentz_projected_el.json"),
    Path("outputs/reports/p0_stueckelberg_connection_force_residual_target.json"),
    Path("outputs/reports/p0_connection_force_weak_congruence_reduction.json"),
    Path("outputs/reports/p0_stueckelberg_projected_cuu_map_force_balance.json"),
    Path("outputs/reports/p0_projected_cuu_action_derivation_target.json"),
    Path("outputs/reports/p0_projected_dust_el_cuu_derivation_chain.json"),
    Path("outputs/reports/p0_effective_density_continuity_pullback_proof.json"),
    Path("outputs/reports/p0_stueckelberg_pulled_dust_el_projection_derivation.json"),
    Path("outputs/reports/p0_pulled_dust_el_cuu_substitution_proof.json"),
    Path("outputs/reports/p0_pulled_dust_el_projection_substitution.json"),
    Path("outputs/reports/p0_dphi_jacobian_volume_identity_target.json"),
    Path("outputs/reports/p0_stueckelberg_density_measure_identity_lock.json"),
    Path("outputs/reports/p0_pulled_dust_dl_velocity_tetrad_substitution_gate.json"),
    Path("outputs/reports/p0_density_measure_branch_decision_gate.json"),
    Path("outputs/reports/p0_b_jphi_qdet_source_measure_branch_selection_target.json"),
    Path("outputs/reports/p0_falpha_free_components_gate.json"),
    Path("outputs/reports/p0_dl_source_law_traceability_gate.json"),
    Path("outputs/reports/p0_b_jphi_qdet_conditional_selection.json"),
    Path("outputs/reports/p0_falpha_minimal_gauge_candidate.json"),
    Path("outputs/reports/p0_b4vol_fminimal_residual_trial.json"),
    Path("outputs/reports/p0_b4vol_residual_remaining_terms.json"),
    Path("outputs/reports/p0_b4vol_janus_source_anchor.json"),
    Path("outputs/reports/p0_falpha_flow_projected_dl_residual_substitution.json"),
    Path("outputs/reports/janus_linear_operator_growth_ic_gate.json"),
    Path("outputs/reports/p0_terminal_blockers_status.json"),
    Path("outputs/reports/p0_constrained_zero_divergence_k_route.json"),
    Path("outputs/reports/p0_bf_connection_constraint_route.json"),
    Path("outputs/reports/p0_optimal_transport_matching_route.json"),
    Path("outputs/reports/p0_blocker_dependency_graph.json"),
    Path("outputs/reports/p0_source_derived_closure_checklist.json"),
    Path("outputs/reports/p0_closure_matrix.json"),
    Path("outputs/reports/bianchi_matter_extension_closure_matrix.json"),
    Path("outputs/reports/bianchi_tensor_matter_extension_target.json"),
    Path("outputs/reports/qcross_geometric_tetrad_map_derivation.json"),
    Path("outputs/reports/qdet_metric_volume_map_derivation.json"),
    Path("outputs/reports/janus_velocity_ic_closure_target.json"),
]
REPORT_PATH = Path("outputs/reports/simulation_readiness_gate.md")
JSON_PATH = Path("outputs/reports/simulation_readiness_gate.json")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_optional_json(path: Path) -> dict | None:
    return load_json(path) if path.exists() else None


def grid_budget_rows(grids: list[int]) -> list[dict]:
    rows = []
    for grid in grids:
        particle_count = 2 * grid**3
        rows.append(
            {
                "grid": grid,
                "particle_count": particle_count,
                "estimated_core_memory_gb": estimate_vectorized_pm_memory_bytes(
                    (grid, grid, grid),
                    particle_count=particle_count,
                )
                / 1024.0**3,
            }
        )
    return rows


def build_payload(
    prediction_gate: dict,
    scaffolds: dict,
    pm_convergence: dict,
    observable_chain: dict,
    survey_interface: dict,
    partial_artifacts: list[dict | None] | None = None,
    grids: list[int] | None = None,
) -> dict:
    grids = [32, 64, 128, 175, 256] if grids is None else grids
    partial_artifacts = [] if partial_artifacts is None else partial_artifacts
    math_blockers = list(prediction_gate.get("blockers", []))
    numerical_ready = bool(pm_convergence.get("controlled_numerical_convergence_ready", False))
    observable_ready = not bool(observable_chain.get("blocking_issue", True))
    survey_ready = bool(survey_interface.get("survey_layer_ready", False))
    parallel_tracks = [
        track["track"]
        for track in scaffolds.get("tracks", [])
        if track.get("parallelizable", False)
    ]
    partial_closures = [
        {
            "description": artifact.get("description", "unknown"),
            "status": artifact.get("status", "recorded"),
            "prediction_ready": bool(artifact.get("prediction_ready", False)),
            "physics_closed": bool(artifact.get("physics_closed", False)),
        }
        for artifact in partial_artifacts
        if artifact is not None
    ]
    open_partial_closures = [
        item for item in partial_closures if not item["physics_closed"] or not item["prediction_ready"]
    ]
    missing_partial_artifacts = len(partial_closures) == 0
    partial_artifacts_ready = bool(partial_closures) and not open_partial_closures
    full_ready = (
        not math_blockers
        and numerical_ready
        and observable_ready
        and survey_ready
        and partial_artifacts_ready
    )
    return {
        "description": "Gate for moving from diagnostic PM runs toward a full Janus cosmological simulation.",
        "full_cosmological_simulation_ready": full_ready,
        "allowed_execution_level": "diagnostic_pm_only" if not full_ready else "candidate_prediction_pipeline",
        "math_blockers": math_blockers,
        "numerical_convergence_ready": numerical_ready,
        "observable_chain_ready": observable_ready,
        "survey_layer_ready": survey_ready,
        "partial_artifacts_ready": partial_artifacts_ready,
        "missing_partial_artifacts": missing_partial_artifacts,
        "partial_closures": partial_closures,
        "open_partial_closures": open_partial_closures,
        "parallel_tracks": parallel_tracks,
        "resource_budget": grid_budget_rows(grids),
        "no_rustine_policy": [
            "no fitted scalar patch for tensor/lensing normalization",
            "no sigma8 normalization claim from the current grid",
            "no raw a-/a+ scale-ratio lensing amplitude",
            "Q_det and Q_cross remain separate factors",
        ],
        "next_actions": [
            "close Bianchi-compatible transport residuals R_plus and R_minus",
            "derive Q_det as a metric-volume density map, not an optical amplitude",
            "derive non-comoving Q_cross from admissible L_minus_to_plus/K_plus transport",
            "close same-L/DL, DlogB4vol, Falpha, and Cuu ledgers before candidate predictions",
            "replace diagnostic ICs with Janus-derived transfer, growth, amplitude and velocity",
            "run controlled PM convergence only after the physics gates are explicit",
        ],
        "verdict": (
            "Full simulation is blocked; diagnostic optimized PM runs may continue."
            if not full_ready
            else "Full simulation gate is open for a candidate prediction pipeline."
        ),
    }


def build_payload_from_files() -> dict:
    return build_payload(
        load_json(PREDICTION_GATE_PATH),
        load_json(SCAFFOLDS_PATH),
        load_json(PM_CONVERGENCE_PATH),
        load_json(OBSERVABLE_CHAIN_PATH),
        load_json(SURVEY_INTERFACE_PATH),
        [load_optional_json(path) for path in PARTIAL_ARTIFACT_PATHS],
    )


def render_markdown(payload: dict) -> str:
    lines = [
        "# Simulation Readiness Gate",
        "",
        payload["description"],
        "",
        f"- full cosmological simulation ready: {payload['full_cosmological_simulation_ready']}",
        f"- allowed execution level: {payload['allowed_execution_level']}",
        f"- numerical convergence ready: {payload['numerical_convergence_ready']}",
        f"- observable chain ready: {payload['observable_chain_ready']}",
        f"- survey layer ready: {payload['survey_layer_ready']}",
        "",
        "## Math Blockers",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["math_blockers"])
    lines.extend(["", "## Partial Closures", ""])
    if payload["partial_closures"]:
        lines.extend(
            f"- {item['description']}: status={item['status']}, "
            f"physics_closed={item['physics_closed']}, "
            f"prediction_ready={item['prediction_ready']}"
            for item in payload["partial_closures"]
        )
    else:
        lines.append("- none")
    lines.extend(["", "## Resource Budget", "", "| grid | particles | core memory GB |", "|---:|---:|---:|"])
    for row in payload["resource_budget"]:
        lines.append(
            f"| {row['grid']} | {row['particle_count']} | "
            f"{row['estimated_core_memory_gb']:.6g} |"
        )
    lines.extend(["", "## No-rustine Policy", ""])
    lines.extend(f"- {item}" for item in payload["no_rustine_policy"])
    lines.extend(["", "## Next Actions", ""])
    lines.extend(f"- {item}" for item in payload["next_actions"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def main() -> None:
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload_from_files()
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
