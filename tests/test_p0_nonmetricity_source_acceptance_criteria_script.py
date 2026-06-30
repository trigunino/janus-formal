from __future__ import annotations

import unittest

from scripts.build_p0_nonmetricity_source_acceptance_criteria import (
    build_payload,
    render_markdown,
)


class P0NonmetricitySourceAcceptanceCriteriaTests(unittest.TestCase):
    def test_acceptance_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonmetricity-source-acceptance-open")
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertLess(payload["criteria_passed"], payload["criteria_total"])

    def test_required_criteria_are_present(self) -> None:
        names = {row["criterion"] for row in build_payload()["criteria"]}

        self.assertIn("published_or_action_source", names)
        self.assertIn("trace_free_channel", names)
        self.assertIn("tracefree_projector_defined", names)
        self.assertIn("tracefree_source_candidates_bounded", names)
        self.assertIn("isotropy_no_go_applied", names)
        self.assertIn("curl_integrability", names)
        self.assertIn("mirror_inverse", names)
        self.assertIn("same_l_qcross_vlasov", names)
        self.assertIn("ghost_stability", names)

    def test_some_algebraic_gates_pass_but_source_gates_do_not(self) -> None:
        rows = {row["criterion"]: row for row in build_payload()["criteria"]}

        self.assertFalse(rows["published_or_action_source"]["passed"])
        self.assertTrue(rows["definition_not_selector"]["passed"])
        self.assertTrue(rows["trace_only_no_go_applied"]["passed"])
        self.assertTrue(rows["tracefree_projector_defined"]["passed"])
        self.assertTrue(rows["tracefree_source_candidates_bounded"]["passed"])
        self.assertTrue(rows["isotropy_no_go_applied"]["passed"])
        self.assertFalse(rows["curl_integrability"]["passed"])
        self.assertTrue(rows["mirror_inverse"]["passed"])

    def test_no_rustine_rules_block_fits_and_trace_promotion(self) -> None:
        rules = " ".join(build_payload()["no_rustine_rules"])

        self.assertIn("no residual-cancel target", rules)
        self.assertIn("no observational fit", rules)
        self.assertIn("no determinant trace", rules)
        self.assertIn("no independent mirror N", rules)

    def test_markdown_reports_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonmetricity Source Acceptance", markdown)
        self.assertIn("Accepted as prediction input: False", markdown)
        self.assertIn("Criteria passed:", markdown)
        self.assertIn("tracefree_projector_defined", markdown)
        self.assertIn("tracefree_source_candidates_bounded", markdown)
        self.assertIn("isotropy_no_go_applied", markdown)
        self.assertIn("p0_tracefree_h_projector_variation_dependency_gate", markdown)
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
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
