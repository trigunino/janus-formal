from __future__ import annotations

import unittest

from scripts.build_bianchi_l_derivative_obstruction import build_payload


class BianchiLDerivativeObstructionTests(unittest.TestCase):
    def test_product_rule_exposes_dl_terms(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["product_rules"])

        self.assertTrue(payload["geodesic_terms_reduced"])
        self.assertTrue(payload["l_derivative_terms_open"])
        self.assertIn("D_minus_nu L_minus_to_plus", rules)
        self.assertIn("D_plus_nu L_plus_to_minus", rules)

    def test_geodesics_close_only_du_terms_not_dl_terms(self) -> None:
        payload = build_payload()
        reductions = " ".join(
            f"{row['closed_piece']} {row['open_piece']}"
            for row in payload["geodesic_reductions"]
        )

        self.assertIn("D_minus_u u_minus", reductions)
        self.assertIn("D_plus_u u_plus", reductions)
        self.assertIn("D_minus_nu L_minus_to_plus", reductions)
        self.assertIn("D_plus_nu L_plus_to_minus", reductions)
        self.assertFalse(payload["residuals_closed"])

    def test_closure_options_are_targets_not_claims(self) -> None:
        payload = build_payload()
        options = " ".join(row["status"] for row in payload["closure_options"])

        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("not derived", options)
        self.assertIn("not a global cosmological proof", options)


if __name__ == "__main__":
    unittest.main()
