from __future__ import annotations

import unittest

from scripts.build_p0_next_session_handoff import (
    build_payload,
    load_upstream_status,
    render_markdown,
)


class P0NextSessionHandoffTests(unittest.TestCase):
    def test_handoff_reports_current_open_state(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "handoff-ready-physics-open")
        self.assertEqual(payload["routes_attacked"], 13)
        self.assertEqual(payload["routes_selecting_phi_j_l"], 0)
        self.assertIn("dependency_fallback", payload)
        self.assertFalse(payload["terminal_blockers_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_open_verrous_and_next_actions_are_actionable(self) -> None:
        payload = build_payload()
        verrou_names = {row["name"] for row in payload["open_verrous"]}
        actions = " ".join(row["action"] for row in payload["next_actions"])

        self.assertIn("source_derived_phi_j_l_selector", verrou_names)
        self.assertIn("split_noether_or_two_sector_identity", verrou_names)
        self.assertIn("same_l_dl_rapidity_transport", verrou_names)
        self.assertIn("b4vol_lapse_slice_selector", verrou_names)
        self.assertIn("tracefree_h_qtf_source", verrou_names)
        self.assertIn("Stueckelberg", actions)
        self.assertIn("no-go", actions)
        self.assertIn("Cartan/BF", actions)
        self.assertIn("trace-free H projector", actions)

    def test_guardrails_and_parallel_agents_are_present(self) -> None:
        payload = build_payload()
        guardrails = " ".join(payload["guardrails"])
        agents = " ".join(payload["parallel_agents"])

        self.assertIn("no observational fit", guardrails)
        self.assertIn("no Q_det/Q_cross", guardrails)
        self.assertIn("no hidden new axiom", guardrails)
        self.assertIn("Agent A", agents)
        self.assertIn("Agent B", agents)
        self.assertIn("Agent C", agents)

    def test_markdown_names_entry_points(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Routes selecting phi/J/L: 0", markdown)
        self.assertIn("p0_non_rustine_closure_research_kernel", markdown)
        self.assertIn("p0_scross_candidate_triage_matrix", markdown)
        self.assertIn("p0_pt_lie_vjanus_ajanus_constraint_solver", markdown)
        self.assertIn("p0_ajanus_branch_selector_dynamics_gate", markdown)
        self.assertIn("p0_ajanus_linear_residual_matching_gate", markdown)
        self.assertIn("p0_ajanus_covariant_lift_obligation", markdown)
        self.assertIn("p0_covariant_q_field_candidate_gate", markdown)
        self.assertIn("p0_relative_strain_q_regular_branch_gate", markdown)
        self.assertIn("p0_relative_strain_dh_lgeom_vs_lorentz_gate", markdown)
        self.assertIn("p0_sigma_dh_equivalence_gate", markdown)
        self.assertIn("p0_sigma_source_traceability_gap_gate", markdown)
        self.assertIn("p0_sigma_trace_only_no_go_gate", markdown)
        self.assertIn("p0_tracefree_h_projector_gate", markdown)
        self.assertIn("p0_tracefree_h_projector_variation_dependency_gate", markdown)
        self.assertIn("p0_tracefree_h_source_candidate_matrix", markdown)
        self.assertIn("p0_tracefree_h_irrep_source_requirements_gate", markdown)
        self.assertIn("p0_tracefree_h_action_operator_requirements_gate", markdown)
        self.assertIn("p0_tracefree_h_closure_obligation_matrix", markdown)
        self.assertIn("p0_tracefree_h_scalar_vector_no_go_gate", markdown)
        self.assertIn("p0_tracefree_h_variational_source_template_gate", markdown)
        self.assertIn("p0_tracefree_h_variational_action_basis_gate", markdown)
        self.assertIn("p0_tracefree_h_action_basis_el_variation_gate", markdown)
        self.assertIn("p0_tracefree_h_action_measure_variation_gate", markdown)
        self.assertIn("p0_tracefree_h_frechet_log_adjoint_gate", markdown)
        self.assertIn("p0_tracefree_h_qtf_to_h_chain_rule_gate", markdown)
        self.assertIn("p0_tracefree_h_quadratic_qtf_h_el_gate", markdown)
        self.assertIn("p0_tracefree_h_linear_qtf_xtf_h_el_gate", markdown)
        self.assertIn("p0_tracefree_h_janus_coupled_stress_stf_transport_gate", markdown)
        self.assertIn("p0_tracefree_h_xtf_source_provenance_variation_contract", markdown)
        self.assertIn("p0_tracefree_h_action_basis_acceptance_filter", markdown)
        self.assertIn("p0_tracefree_h_linear_coupling_rank_gate", markdown)
        self.assertIn("p0_tracefree_h_derivative_branch_stability_gate", markdown)
        self.assertIn("p0_tracefree_h_linear_xtf_provenance_gate", markdown)
        self.assertIn("p0_tracefree_h_same_bridge_dependency_gate", markdown)
        self.assertIn("p0_tracefree_h_source_action_provenance_chain_gate", markdown)
        self.assertIn("p0_tracefree_h_derivation_attack_plan", markdown)
        self.assertIn("p0_tracefree_h_anisotropic_stress_gate", markdown)
        self.assertIn("p0_tracefree_h_weyl_shear_source_gate", markdown)
        self.assertIn("p0_tracefree_h_vlasov_quadrupole_gate", markdown)
        self.assertIn("p0_tracefree_h_relative_strain_action_gate", markdown)
        self.assertIn("p0_tracefree_h_bf_gl_phi_sigma_gate", markdown)
        self.assertIn("p0_tracefree_h_isotropy_no_go_gate", markdown)
        self.assertIn("p0_h_strain_action_variation_gate", markdown)
        self.assertIn("p0_h_strain_ghost_symbolic_gate", markdown)
        self.assertIn("p0_nonmetricity_integrability_curl_gate", markdown)
        self.assertIn("p0_nonmetricity_curl_numeric_probe", markdown)
        self.assertIn("p0_nonmetricity_mirror_inverse_gate", markdown)
        self.assertIn("p0_phi_sigma_source_action_decision_gate", markdown)
        self.assertIn("p0_nonmetricity_source_acceptance_criteria", markdown)
        self.assertIn("p0_nonmetricity_rank_reduction_ledger", markdown)
        self.assertIn("p0_relative_metric_nonmetricity_sigma_dh_gate", markdown)
        self.assertIn("p0_stueckelberg_sigma_dh_variation_rank_gate", markdown)
        self.assertIn("p0_cartan_bf_gl_strain_selector_gate", markdown)
        self.assertIn("p0_sigma_source_selector_attack_matrix", markdown)
        self.assertIn("p0_relative_strain_q_derivative_omega_gate", markdown)
        self.assertIn("p0_action_ghost_stability_gate", markdown)
        self.assertIn("weak-field linear residual matching", markdown)
        self.assertIn("p0_minimal_janus_soldering_principle_candidate", markdown)
        self.assertIn("p0_bf_connection_constraint_route", markdown)
        self.assertIn("p0_stueckelberg_two_diffeo_route", markdown)
        self.assertIn("p0_zero_rustine_phi_j_l_route_attack_matrix", markdown)
        self.assertIn("Recommended start", markdown)
        self.assertIn("Verdict:", markdown)

    def test_upstream_fallback_is_conservative(self) -> None:
        matrix, terminal, _fallback = load_upstream_status()

        self.assertEqual(matrix["routes_attacked"], 13)
        self.assertEqual(matrix["routes_selecting_phi_j_l"], 0)
        self.assertNotEqual(terminal["status"], "terminal-blockers-closed")


if __name__ == "__main__":
    unittest.main()
