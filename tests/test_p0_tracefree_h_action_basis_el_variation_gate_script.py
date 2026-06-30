from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_action_basis_el_variation_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHActionBasisELVariationGateTests(unittest.TestCase):
    def test_gate_is_open_formal_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-action-basis-el-variation-gate-open",
        )
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertEqual(payload["ledger_scope"], "formal candidate variations only")
        self.assertTrue(payload["all_variations_formal"])
        self.assertFalse(payload["any_variation_accepted"])
        self.assertFalse(payload["residual_target_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_requested_formal_variations_are_recorded(self) -> None:
        rows = {row["term"]: row for row in build_payload()["formal_variations"]}

        self.assertEqual(len(rows), 6)
        self.assertEqual(rows["tr_qtf2"]["projected_el_source"], "2 Q_TF")
        self.assertEqual(rows["tr_qtf3"]["projected_el_source"], "3 P_STF(Q_TF^2)")
        self.assertEqual(
            rows["dqtf_kinetic"]["projected_el_source"],
            "-2 P_STF(D*D Q_TF)",
        )
        self.assertEqual(
            rows["dhtf_kinetic"]["projected_el_source"],
            "-2 P_STF(D*D H_TF)",
        )
        self.assertIn("X_TF plus dependency terms", rows["qtf_xtf_linear"]["projected_el_source"])
        self.assertIn("constraint multiplier source", rows["bf_gl_constraints"]["projected_el_source"])

    def test_every_variation_is_conditional_and_unaccepted(self) -> None:
        rows = build_payload()["formal_variations"]

        self.assertTrue(all(row["status"] == "formal/conditional" for row in rows))
        self.assertFalse(any(row["accepted"] for row in rows))
        self.assertEqual(build_payload()["accepted_variations"], [])

    def test_dependency_and_constraint_rules_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("H, L, phi, or matter", payload["dependency_rule"])
        self.assertIn("Janus-derived", payload["constraint_rule"])
        rows = {row["term"]: row for row in payload["formal_variations"]}
        self.assertIn("depends on H, L, phi, or matter", rows["qtf_xtf_linear"]["condition"])
        self.assertIn("Janus", rows["bf_gl_constraints"]["condition"])

    def test_residual_target_and_determinant_trace_are_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["residual_target_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertIn("residual target", forbidden)
        self.assertIn("determinant trace", forbidden)
        self.assertIn("log det(H)", forbidden)
        self.assertIn("B4vol", forbidden)

    def test_markdown_reports_ledger_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action-Basis EL Variation", markdown)
        self.assertIn("delta Tr(Q_TF^2) -> 2 Q_TF", markdown)
        self.assertIn("delta Tr(Q_TF^3) -> 3 P_STF(Q_TF^2)", markdown)
        self.assertIn("delta (D Q_TF)^2 -> -2 P_STF(D*D Q_TF) + boundary", markdown)
        self.assertIn("delta (D H_TF)^2 -> -2 P_STF(D*D H_TF) + boundary", markdown)
        self.assertIn("Residual target allowed: False", markdown)
        self.assertIn("Determinant trace allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
