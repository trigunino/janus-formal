from __future__ import annotations

import unittest

from scripts.build_p0_noether_split_rank_obstruction import (
    build_payload,
    render_markdown,
)


class P0NoetherSplitRankObstructionTests(unittest.TestCase):
    def test_single_diagonal_identity_is_rank_one_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "single-diagonal-noether-rank-one-obstruction-proved")
        self.assertEqual(payload["diagonal_identity_rank"], 1)
        self.assertEqual(payload["diagonal_identity_nullity"], 1)
        self.assertFalse(payload["single_identity_can_force_rplus_zero"])
        self.assertFalse(payload["single_identity_can_force_rminus_zero"])
        self.assertFalse(payload["single_identity_can_force_both_residuals_zero"])
        self.assertTrue(payload["combined_residual_constrained"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_kernel_counterexample_blocks_separate_residual_zeros(self) -> None:
        payload = build_payload()
        rows = {row["step"]: row for row in payload["proof_rows"]}

        self.assertEqual(payload["counterexample_residual"], ["1", "-1"])
        self.assertEqual(payload["counterexample_combined_value"], "0")
        self.assertTrue(payload["counterexample_has_nonzero_separate_residuals"])
        self.assertTrue(rows["kernel_counterexample"]["closed"])
        self.assertIn("R_plus + R_minus = 0", rows["kernel_counterexample"]["formula"])
        self.assertIn("nonzero", rows["kernel_counterexample"]["meaning"])

    def test_split_closure_requires_independent_identity_or_source_equation(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["split_rows_rank"], 2)
        self.assertEqual(payload["contrast_rows_rank"], 2)
        self.assertFalse(payload["independent_sector_identity_available"])
        self.assertFalse(payload["source_derived_split_equation_available"])
        self.assertTrue(payload["requires_independent_sector_identity_or_source_split"])
        self.assertIn("source-derived split equation", payload["verdict"])

    def test_zero_rustine_rules_forbid_shortcuts(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["zero_rustine_rules"])
        markdown = render_markdown(payload)

        self.assertTrue(payload["bounded_artifact"])
        self.assertTrue(payload["zero_rustine"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["uses_hidden_axiom"])
        self.assertIn("observational fit", rules)
        self.assertIn("Q_det/Q_cross absorption", rules)
        self.assertIn("hidden axiom", rules)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
