from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_stress_response_target import build_payload


class P0LinearImatterStressResponseTargetTests(unittest.TestCase):
    def test_response_target_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "stress-response-target-open")
        self.assertTrue(payload["measure_trace_closed"])
        self.assertFalse(payload["same_sector_stress_response_closed"])
        self.assertFalse(payload["solder_metric_response_closed"])
        self.assertFalse(payload["pulled_stress_response_closed"])
        self.assertFalse(payload["mirror_response_closed"])
        self.assertTrue(payload["matter_action_stress_response_target_available"])
        self.assertFalse(payload["full_k_variation_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_terms_cover_stress_l_pullback_and_mirror(self) -> None:
        text = " ".join(row["formula"] for row in build_payload()["response_terms"])

        self.assertIn("delta_g T_plus", text)
        self.assertIn("delta_g L", text)
        self.assertIn("pullback/Jacobian", text)
        self.assertIn("plus/minus exchanged", text)

    def test_rules_forbid_scalar_absorption(self) -> None:
        rules = " ".join(build_payload()["closure_rules"])

        self.assertIn("measure_trace", rules)
        self.assertIn("Q_cross/Q_det", rules)
        self.assertIn("pressure", rules)
        self.assertIn("R_plus/R_minus", rules)


if __name__ == "__main__":
    unittest.main()
