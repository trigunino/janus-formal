from __future__ import annotations

import unittest

from scripts.build_p0_source_pullback_metric_response_target import build_payload


class P0SourcePullbackMetricResponseTargetTests(unittest.TestCase):
    def test_receiver_metric_branch_closed_but_action_bridge_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "receiver-metric-branch-closed-action-bridge-open")
        self.assertTrue(payload["receiver_metric_fixed_phi_source_branch_closed"])
        self.assertTrue(payload["receiver_b4vol_response_closed"])
        self.assertTrue(payload["source_metric_response_separate_closed"])
        self.assertTrue(payload["phi_variation_separated_from_metric_k"])
        self.assertTrue(payload["rho_to_fixed_source_branch_closed"])
        self.assertFalse(payload["pulled_action_bridge_closed"])
        self.assertFalse(payload["full_pullback_density_response_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_separate_receiver_source_and_phi_variations(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["variation_rows"])

        self.assertIn("delta_{g_receiver}", text)
        self.assertIn("delta_{g_source}", text)
        self.assertIn("delta_phi", text)
        self.assertIn("Lie_{delta phi}", text)
        self.assertIn("open-action-required", text)


if __name__ == "__main__":
    unittest.main()
