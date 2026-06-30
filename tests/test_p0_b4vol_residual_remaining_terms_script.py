from __future__ import annotations

import unittest

from scripts.build_p0_b4vol_residual_remaining_terms import build_payload


class P0B4volResidualRemainingTermsTests(unittest.TestCase):
    def test_product_rule_terms_are_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "b4vol-product-rule-open")
        self.assertTrue(payload["b4vol_product_rule_written"])
        self.assertFalse(payload["dlogb_identity_source_derived"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_plus_and_minus_residuals_include_d_bk_product_rule(self) -> None:
        expanded = " ".join(row["expanded"] for row in build_payload()["product_rule_residuals"])

        self.assertIn("D_plus(B_4vol_plus_from_minus K_minus_to_plus)", expanded)
        self.assertIn("K_minus_to_plus D_plus B_4vol", expanded)
        self.assertIn("D_minus(B_4vol_minus_from_plus K_plus_to_minus)", expanded)
        self.assertIn("K_plus_to_minus D_minus B_4vol", expanded)

    def test_dlogb_required_pieces_keep_lapse_and_spatial_determinant(self) -> None:
        pieces = " ".join(build_payload()["dlogb_required_pieces"])

        self.assertIn("D log N", pieces)
        self.assertIn("spatial determinant", pieces)
        self.assertIn("gamma", pieces)
        self.assertIn("lapse proof", pieces)


if __name__ == "__main__":
    unittest.main()
