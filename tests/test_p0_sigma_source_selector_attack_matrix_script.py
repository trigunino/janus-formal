from __future__ import annotations

import unittest

from scripts.build_p0_sigma_source_selector_attack_matrix import (
    build_payload,
    render_markdown,
)


class P0SigmaSourceSelectorAttackMatrixTests(unittest.TestCase):
    def test_matrix_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sigma-source-selector-open")
        self.assertTrue(payload["sigma_dh_equivalence_closed"])
        self.assertEqual(payload["routes_attacked"], 10)
        self.assertEqual(payload["routes_selecting_sigma_dh"], 0)
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_conditional_routes_are_named(self) -> None:
        routes = set(build_payload()["conditional_routes"])

        self.assertIn("relative_metric_nonmetricity", routes)
        self.assertIn("stueckelberg_gl_h_extension", routes)
        self.assertIn("cartan_bf_gl_strain_connection", routes)
        self.assertIn("h_strain_derivative_action", routes)
        self.assertIn("matter_vlasov_anisotropic_stress", routes)

    def test_rejects_lorentz_trace_only_and_fit_routes(self) -> None:
        rows = {row["route"]: row for row in build_payload()["routes"]}

        self.assertFalse(rows["pure_lorentz_omega"]["selects_sigma_dh"])
        self.assertIn("D H=0", rows["pure_lorentz_omega"]["verdict"])
        self.assertFalse(rows["stueckelberg_two_diffeo_action"]["selects_sigma_dh"])
        self.assertIn("zero direct rank", rows["stueckelberg_two_diffeo_action"]["verdict"])
        self.assertFalse(rows["determinant_b4vol_trace_only"]["selects_sigma_dh"])
        self.assertIn("Tr(Q)", rows["determinant_b4vol_trace_only"]["verdict"])
        self.assertFalse(rows["observational_residual_cancellation"]["zero_rustine"])

    def test_required_closure_tests_keep_same_l_and_ghost_gate(self) -> None:
        tests = " ".join(build_payload()["required_closure_tests"])

        self.assertIn("p0_sigma_source_traceability_gap_gate", tests)
        self.assertIn("p0_sigma_trace_only_no_go_gate", tests)
        self.assertIn("p0_tracefree_h_projector_gate", tests)
        self.assertIn("p0_tracefree_h_projector_variation_dependency_gate", tests)
        self.assertIn("delta P_STF", tests)
        self.assertIn("p0_tracefree_h_source_candidate_matrix", tests)
        self.assertIn("Q_TF irrep", tests)
        self.assertIn("action-operator", tests)
        self.assertIn("p0_tracefree_h_closure_obligation_matrix", tests)
        self.assertIn("scalar/vector no-go", tests)
        self.assertIn("variational source template", tests)
        self.assertIn("variational action basis", tests)
        self.assertIn("action-basis EL variation", tests)
        self.assertIn("action-measure variation gate", tests)
        self.assertIn("FrechetLog adjoint gate", tests)
        self.assertIn("Q_TF-to-H chain rule", tests)
        self.assertIn("quadratic Q_TF H-EL gate", tests)
        self.assertIn("linear Q_TF X_TF H-EL gate", tests)
        self.assertIn("Janus coupled-stress STF transport gate", tests)
        self.assertIn("X_TF source provenance variation contract", tests)
        self.assertIn("acceptance filter", tests)
        self.assertIn("linear coupling rank", tests)
        self.assertIn("derivative branch stability", tests)
        self.assertIn("linear X_TF provenance", tests)
        self.assertIn("same-bridge dependency", tests)
        self.assertIn("source-action provenance chain", tests)
        self.assertIn("derivation attack plan", tests)
        self.assertIn("Pi_TF", tests)
        self.assertIn("Weyl/shear", tests)
        self.assertIn("Vlasov", tests)
        self.assertIn("relative-strain-action", tests)
        self.assertIn("BF/GL Phi_Sigma", tests)
        self.assertIn("p0_tracefree_h_isotropy_no_go_gate", tests)
        self.assertIn("p0_h_strain_action_variation_gate", tests)
        self.assertIn("p0_h_strain_ghost_symbolic_gate", tests)
        self.assertIn("p0_nonmetricity_integrability_curl_gate", tests)
        self.assertIn("p0_nonmetricity_curl_numeric_probe", tests)
        self.assertIn("p0_nonmetricity_mirror_inverse_gate", tests)
        self.assertIn("p0_phi_sigma_source_action_decision_gate", tests)
        self.assertIn("Janus source/action", tests)
        self.assertIn("trace-free Q_TF", tests)
        self.assertIn("mirror inverse", tests)
        self.assertIn("same L", tests)
        self.assertIn("ghost/stability", tests)

    def test_markdown_reports_matrix(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sigma Source Selector", markdown)
        self.assertIn("Routes selecting Sigma/DH: 0", markdown)
        self.assertIn("relative_metric_nonmetricity", markdown)
        self.assertIn("stueckelberg_gl_h_extension", markdown)
        self.assertIn("h_strain_derivative_action", markdown)
        self.assertIn("Forbidden Routes", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
