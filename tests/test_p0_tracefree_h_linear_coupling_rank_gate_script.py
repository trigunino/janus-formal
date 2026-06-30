from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_linear_coupling_rank_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHLinearCouplingRankGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-linear-coupling-rank-source-gate-open",
        )
        self.assertFalse(payload["all_requirements_closed"])
        self.assertFalse(payload["any_candidate_accepted"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_linear_coupling_requires_same_bridge_source_derived_stf_rank2(self) -> None:
        payload = build_payload()
        requirements = payload["x_tf_requirements"]

        self.assertEqual(payload["linear_coupling"], "int Q_TF^{ab} X_TF_ab")
        self.assertIn("covariant symmetric trace-free rank-2", payload["acceptance_rule"])
        self.assertIn("same bridge", payload["acceptance_rule"])
        self.assertIn("source-derived", payload["acceptance_rule"])
        self.assertTrue(requirements["covariant"])
        self.assertTrue(requirements["symmetric_trace_free"])
        self.assertTrue(requirements["rank_2"])
        self.assertTrue(requirements["same_bridge"])
        self.assertTrue(requirements["source_derived"])
        self.assertFalse(requirements["residual_target_allowed"])

    def test_rank_count_distinguishes_covariant_and_spatial_stf(self) -> None:
        rank = build_payload()["rank_count"]

        self.assertEqual(rank["symmetric_rank_4d"], 10)
        self.assertEqual(rank["trace_rank"], 1)
        self.assertEqual(rank["covariant_stf_rank_4d"], 9)
        self.assertEqual(rank["spatial_stf_rank_after_u_choice"], 5)

    def test_requested_candidates_are_conditional_not_accepted(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["candidates"]}

        self.assertEqual(rows["Pi_TF"]["rank_source_status"], "spatial/conditional")
        self.assertEqual(rows["Weyl_shear"]["rank_source_status"], "diagnostic/conditional")
        self.assertEqual(rows["Vlasov_quadrupole"]["rank_source_status"], "hierarchy/conditional")
        self.assertEqual(rows["Phi_Sigma"]["rank_source_status"], "source/action/conditional")
        self.assertTrue(all(row["can_source_h_tf"] == "conditional" for row in rows.values()))
        self.assertIn("spatial STF", rows["Pi_TF"]["blocker"])
        self.assertIn("diagnostic", rows["Weyl_shear"]["blocker"])
        self.assertIn("Vlasov hierarchy", rows["Vlasov_quadrupole"]["blocker"])
        self.assertIn("source/action", rows["Phi_Sigma"]["blocker"])

    def test_scalars_determinant_trace_and_residual_xtf_fail(self) -> None:
        payload = build_payload()
        rejected = {row["route"]: row for row in payload["rejected_routes"]}
        guardrails = " ".join(payload["guardrails"])

        self.assertFalse(payload["scalars_can_source_h_tf"])
        self.assertFalse(payload["determinant_trace_can_source_h_tf"])
        self.assertFalse(payload["residual_x_tf_allowed"])
        self.assertFalse(rejected["density_or_pressure_scalar"]["accepted"])
        self.assertFalse(rejected["determinant_trace"]["accepted"])
        self.assertFalse(rejected["residual_x_tf"]["accepted"])
        self.assertIn("scalar", rejected["density_or_pressure_scalar"]["reason"])
        self.assertIn("trace", rejected["determinant_trace"]["reason"])
        self.assertIn("source-derived", rejected["residual_x_tf"]["reason"])
        self.assertIn("residual X_TF", guardrails)

    def test_markdown_reports_gate_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Linear Coupling Rank Gate", markdown)
        self.assertIn("Linear coupling: `int Q_TF^{ab} X_TF_ab`", markdown)
        self.assertIn("Residual X_TF allowed: False", markdown)
        self.assertIn("Pi_TF", markdown)
        self.assertIn("Phi_Sigma", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
