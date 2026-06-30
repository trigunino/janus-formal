from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_metric_variation import build_payload


class P0LinearImatterMetricVariationTests(unittest.TestCase):
    def test_measure_variation_closed_but_full_k_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "measure-variation-closed-full-k-open")
        self.assertTrue(payload["measure_variation_closed"])
        self.assertTrue(payload["partial_metric_variation_available"])
        self.assertFalse(payload["frozen_matter_trace_is_full_k"])
        self.assertTrue(payload["requires_stress_response"])
        self.assertTrue(payload["requires_l_metric_dependence"])
        self.assertTrue(payload["requires_pullback_metric_dependence"])
        self.assertTrue(payload["stress_response_target_available"])
        self.assertTrue(payload["conditional_dust_k_variation_available"])
        self.assertFalse(payload["full_metric_variation_closed"])
        self.assertFalse(payload["k_plus_k_minus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_keep_measure_trace_separate_from_k(self) -> None:
        rows = {row["row"]: row for row in build_payload()["variation_rows"]}

        self.assertIn("sqrt(-g_plus)", rows["measure_variation"]["formula"])
        self.assertIn("diagnostic-only", rows["frozen_matter_trace"]["status"])
        self.assertIn("delta_g T_plus", rows["full_k_plus"]["formula"])
        self.assertIn("delta_g L", rows["full_k_plus"]["formula"])
        self.assertIn("mirror metric response", rows["full_k_minus"]["formula"])


if __name__ == "__main__":
    unittest.main()
