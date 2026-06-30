from __future__ import annotations

import unittest

from scripts.build_p0_linear_imatter_l_variation import build_payload


class P0LinearImatterLVariationTests(unittest.TestCase):
    def test_l_variation_algebra_closed_projection_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "l-variation-and-lorentz-projection-closed")
        self.assertTrue(payload["delta_l_algebra_closed"])
        self.assertTrue(payload["raw_e_l_available"])
        self.assertTrue(payload["lorentz_projected_e_l_closed"])
        self.assertFalse(payload["split_noether_residuals_evaluated"])
        self.assertFalse(payload["prediction_ready"])

    def test_variation_rows_include_delta_l_symmetric_and_projection(self) -> None:
        rows = {row["row"]: row for row in build_payload()["variation_rows"]}

        self.assertIn("L_mu^a T_minus_ab L_nu^b", rows["plus_contract"]["formula"])
        self.assertIn("deltaL_mu^a", rows["delta_l"]["formula"])
        self.assertIn("2 T_plus", rows["symmetric_stress_reduction"]["formula"])
        self.assertIn("E_L_mu^a", rows["e_l_raw"]["formula"])
        self.assertIn("antisym_ab", rows["lorentz_projection"]["formula"])


if __name__ == "__main__":
    unittest.main()
