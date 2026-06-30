from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_irrep_source_requirements_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHIrrepSourceRequirementsGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-irrep-source-requirements-open")
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["conditional_routes_closed"])
        self.assertFalse(payload["residual_fit_allowed"])
        self.assertFalse(payload["residual_fit_used"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_4d_irrep_requirement_is_stf_rank2_in_same_bridge(self) -> None:
        payload = build_payload()
        count = payload["component_count"]

        self.assertEqual(payload["dimension"], 4)
        self.assertEqual(count["symmetric_rank2_components"], 10)
        self.assertEqual(count["trace_components"], 1)
        self.assertEqual(count["stf_rank2_components"], 9)
        self.assertTrue(payload["same_receiver_source_bridge_required"])
        self.assertTrue(payload["covariant_stf_rank2_required"])
        self.assertIn("symmetric trace-free rank-2 tensor", payload["irreducible_source_requirement"])
        self.assertIn("same receiver/source bridge", payload["irreducible_source_requirement"])

    def test_scalars_have_zero_stf_projection(self) -> None:
        rows = {row["source"]: row for row in build_payload()["scalar_routes"]}

        self.assertEqual(set(rows), {"rho", "p", "B4vol", "Q_det"})
        self.assertTrue(build_payload()["scalar_stf_projection_zero"])
        self.assertTrue(all("P_STF" in row["stf_projection"] for row in rows.values()))
        self.assertTrue(all(row["stf_projection"].endswith("=0") for row in rows.values()))
        self.assertFalse(any(row["selects_h_tf_q_tf"] for row in rows.values()))

    def test_vectors_gradients_and_conditional_routes_underselect(self) -> None:
        payload = build_payload()
        non_tensor = {row["source"]: row for row in payload["non_tensor_routes"]}
        conditional = {row["source"]: row for row in payload["conditional_routes"]}

        self.assertFalse(payload["vectors_gradients_select_covariant_stf_without_law"])
        self.assertIn("vectors", non_tensor)
        self.assertIn("gradients", non_tensor)
        self.assertTrue(all("derivative/gauge/action law" in row["blocker"] for row in non_tensor.values()))
        self.assertTrue(payload["spatial_pi_tf_selects_only_after_congruence_gauge"])
        self.assertEqual(conditional["spatial_Pi_TF"]["status"], "conditional")
        self.assertIn("Weyl_shear", conditional)
        self.assertIn("Vlasov_quadrupole", conditional)
        self.assertIn("relative_H_Q_action", conditional)
        self.assertIn("BF_GL_Phi_Sigma", conditional)
        self.assertTrue(all(row["status"] == "conditional" for row in conditional.values()))

    def test_markdown_reports_requirements_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Irrep Source Requirements", markdown)
        self.assertIn("same receiver/source bridge", markdown)
        self.assertIn("P_STF(rho g_ab)=0", markdown)
        self.assertIn("vectors", markdown)
        self.assertIn("gradients", markdown)
        self.assertIn("spatial_Pi_TF", markdown)
        self.assertIn("Weyl_shear", markdown)
        self.assertIn("Vlasov_quadrupole", markdown)
        self.assertIn("BF_GL_Phi_Sigma", markdown)
        self.assertIn("Residual fit allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
