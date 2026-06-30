from __future__ import annotations

import unittest

from scripts.build_p0_dust_pullback_density_response_bridge import build_payload


class P0DustPullbackDensityResponseBridgeTests(unittest.TestCase):
    def test_bridge_closes_bookkeeping_not_full_response(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pullback-density-response-bridge-open")
        self.assertTrue(payload["field_source_measure_anchored"])
        self.assertTrue(payload["effective_current_continuity_closed"])
        self.assertTrue(payload["density_response_chain_rule_closed"])
        self.assertTrue(payload["receiver_measure_response_closed"])
        self.assertFalse(payload["source_pullback_metric_response_closed"])
        self.assertTrue(payload["source_pullback_metric_response_target_available"])
        self.assertTrue(payload["no_double_counting_rule_closed"])
        self.assertFalse(payload["full_pullback_density_response_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_b4vol_chain_rule_and_no_double_counting(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["bridge_rows"])

        self.assertIn("rho_eff = B_4vol rho_to", text)
        self.assertIn("delta_g rho_eff", text)
        self.assertIn("sqrt|g_receiver|", text)
        self.assertIn("source metric variation", text)
        self.assertIn("do not multiply Q_det/B_4vol again", text)


if __name__ == "__main__":
    unittest.main()
