from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_conditional_dust_k_variation import build_payload


class P0LinearImatterConditionalDustKVariationTests(unittest.TestCase):
    def test_conditional_k_kernel_is_partial_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-dust-k-kernel-partial")
        self.assertTrue(payload["measure_piece_closed"])
        self.assertTrue(payload["same_sector_dust_piece_closed_under_branch"])
        self.assertFalse(payload["pulled_m_piece_closed"])
        self.assertTrue(payload["pulled_m_metric_response_target_available"])
        self.assertFalse(payload["delta_g_l_closed"])
        self.assertFalse(payload["mirror_minus_variation_closed"])
        self.assertTrue(payload["available_k_kernel_partial"])
        self.assertFalse(payload["full_k_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_include_kernel_and_open_pulled_m(self) -> None:
        text = " ".join(row["formula"] + row["status"] for row in build_payload()["k_rows"])

        self.assertIn("K_kernel", text)
        self.assertIn("rho_plus", text)
        self.assertIn("delta_g M_minus_to_plus", text)
        self.assertIn("delta-g-L", text)
        self.assertIn("not full K_plus", text)


if __name__ == "__main__":
    unittest.main()
