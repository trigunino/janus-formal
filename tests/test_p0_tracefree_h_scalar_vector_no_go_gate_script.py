from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_scalar_vector_no_go_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHScalarVectorNoGoGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-scalar-vector-low-derivative-no-go-open",
        )
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["residual_fit_allowed"])
        self.assertFalse(payload["residual_fit_used"])
        self.assertFalse(payload["determinant_trace_absorption_allowed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_component_count_keeps_stf_rank_nine_target(self) -> None:
        payload = build_payload()
        count = payload["component_count"]

        self.assertEqual(payload["dimension"], 4)
        self.assertEqual(count["symmetric_rank2_components"], 10)
        self.assertEqual(count["trace_components"], 1)
        self.assertEqual(count["stf_rank2_components"], 9)
        self.assertIn("symmetric trace-free rank-2", payload["target_source"])

    def test_local_scalar_sources_are_trace_only_with_zero_stf_projection(self) -> None:
        payload = build_payload()
        rows = {row["source"]: row for row in payload["scalar_sources"]}

        self.assertEqual(set(rows), {"rho", "p", "B4vol", "Q_det"})
        self.assertTrue(payload["local_scalars_produce_trace_only_metric_terms"])
        self.assertTrue(payload["scalar_stf_projection_zero"])
        self.assertTrue(all(row["metric_term"].endswith("g_ab") for row in rows.values()))
        self.assertTrue(all(row["stf_projection"].endswith("=0") for row in rows.values()))
        self.assertFalse(any(row["selects_h_tf_q_tf"] for row in rows.values()))

    def test_single_vector_and_gradient_do_not_covariantly_select_stf_rank2(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["vector_gradient_routes"]}

        self.assertFalse(payload["single_vector_gradient_covariant_stf_selector"])
        self.assertEqual(set(rows), {"single_vector", "single_gradient"})
        self.assertTrue(all("symmetric trace-free rank-2" in row["blocker"] for row in rows.values()))
        self.assertTrue(all("metric/projector/gauge/action law" in row["blocker"] for row in rows.values()))
        self.assertFalse(any(row["selects_h_tf_q_tf"] for row in rows.values()))

    def test_hessian_and_gradient_square_are_unaccepted_derivative_ansatz(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["derivative_ansatz_routes"]}
        guardrails = " ".join(payload["guardrails"])

        self.assertFalse(payload["derivative_ansatz_accepted"])
        self.assertTrue(payload["janus_source_action_required_for_derivative_ansatz"])
        self.assertTrue(payload["boundary_gauge_required_for_derivative_ansatz"])
        self.assertEqual(set(rows), {"hessian_stf", "gradient_square_stf"})
        self.assertTrue(all(row["classification"] == "derivative ansatz" for row in rows.values()))
        self.assertTrue(all(row["requirement"] == "Janus source/action plus boundary/gauge" for row in rows.values()))
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("residual fitting", guardrails)
        self.assertIn("determinant trace", guardrails)

    def test_markdown_reports_no_go_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Scalar/Vector Low-Derivative No-Go", markdown)
        self.assertIn("P_STF(rho g_ab)=0", markdown)
        self.assertIn("single_vector", markdown)
        self.assertIn("single_gradient", markdown)
        self.assertIn("hessian_stf", markdown)
        self.assertIn("gradient_square_stf", markdown)
        self.assertIn("Residual fit allowed: False", markdown)
        self.assertIn("Determinant trace absorption allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
