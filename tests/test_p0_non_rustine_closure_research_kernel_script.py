from __future__ import annotations

import unittest

from scripts.build_p0_non_rustine_closure_research_kernel import (
    build_payload,
    render_markdown,
)


class P0NonRustineClosureResearchKernelTests(unittest.TestCase):
    def test_kernel_blocks_free_choice_and_predictions(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "infrastructure-ready-physics-open")
        self.assertTrue(payload["source_action_required"])
        self.assertFalse(payload["free_choice_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_selection_rule_distinguishes_forced_from_hand_chosen(self) -> None:
        distinction = build_payload()["distinction"]

        self.assertIn("variational principle", distinction["allowed_selection"])
        self.assertIn("symmetry/Noether", distinction["allowed_selection"])
        self.assertIn("Choose S_cross", distinction["forbidden_choice"])
        self.assertIn("improves data agreement", distinction["forbidden_choice"])

    def test_pt_lie_is_useful_but_not_sufficient(self) -> None:
        assessment = " ".join(
            row["idea"] + " " + row["useful_for"] + " " + row["not_enough_for"]
            for row in build_payload()["pt_lie_assessment"]
        )

        self.assertIn("PT/Lie/Poincare", assessment)
        self.assertIn("phi", assessment)
        self.assertIn("L", assessment)
        self.assertIn("action", assessment)
        self.assertIn("variational coupling", assessment)

    def test_routes_include_action_bf_no_go_and_ghost_gate(self) -> None:
        routes = " ".join(row["route"] + " " + row["success_gate"] for row in build_payload()["closure_routes"])

        self.assertIn("source-derived action", routes)
        self.assertIn("S_cross candidate triage", routes)
        self.assertIn("Cartan/BF", routes)
        self.assertIn("no-go theorem", routes)
        self.assertIn("stability/ghost gate", routes)
        self.assertIn("no ghost", routes)

    def test_markdown_names_agents_and_acceptance_tests(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Next Agent Tasks", markdown)
        self.assertIn("Agent A", markdown)
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
        self.assertIn("R_plus=0", markdown)
        self.assertIn("R_minus=0", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
