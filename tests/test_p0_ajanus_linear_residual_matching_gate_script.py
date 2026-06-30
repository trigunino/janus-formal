from __future__ import annotations

import unittest

from scripts.build_p0_ajanus_linear_residual_matching_gate import (
    build_payload,
    render_markdown,
)


class P0AjanusLinearResidualMatchingGateTests(unittest.TestCase):
    def test_gate_selects_p_like_conditionally_not_globally(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "weakfield-linear-matching-selects-p-like-conditionally",
        )
        self.assertEqual(
            payload["conditional_selected_branch"],
            "P-like odd A_Janus for weak-field non-equal linear residuals",
        )
        self.assertTrue(payload["janus_source_requires_linear_transport"])
        self.assertFalse(payload["global_branch_selected_by_full_janus_source"])
        self.assertFalse(payload["prediction_ready"])

    def test_symbolic_matching_rejects_pt_like_for_nonzero_linear_residual(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["source_residual_model"], "q**2*r2 + q*r1")
        self.assertEqual(payload["p_like_linear_match_condition"], "-a1 + r1=0 -> a1=r1")
        self.assertEqual(payload["pt_like_linear_residual"], "r1")
        self.assertFalse(payload["pt_like_can_match_nonzero_linear_residual"])
        self.assertEqual(payload["covariant_lift_next_artifact"], "p0_ajanus_covariant_lift_obligation")

    def test_weakfield_rows_are_available_and_linear(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["weakfield_source_rows_available"])
        self.assertTrue(payload["weakfield_rows_are_linear_in_potential_difference"])
        self.assertIn("H_Phi_minus", payload["weakfield_source_examples"])
        self.assertIn("H_Psi_minus", payload["weakfield_source_examples"])

    def test_markdown_reports_scope_and_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Linear Residual Matching", markdown)
        self.assertIn("PT-like can match nonzero linear residual: False", markdown)
        self.assertIn("conditional weak-field", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
