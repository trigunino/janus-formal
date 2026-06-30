from __future__ import annotations

import unittest

from scripts.build_p0_connection_difference_cuu_identity import build_payload, render_markdown


class P0ConnectionDifferenceCuuIdentityTests(unittest.TestCase):
    def test_connection_difference_residuals_close(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "connection-difference-cuu-identity-closed-algebraic")
        self.assertTrue(payload["residuals_zero"])
        self.assertTrue(payload["plus_sign_closed"])
        self.assertTrue(payload["minus_sign_closed"])
        self.assertTrue(payload["cross_pullback_algebra_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_have_zero_residuals_and_signs(self) -> None:
        rows = {row["row"]: row for row in build_payload()["rows"]}

        self.assertEqual(rows["plus_receiver_minus_source"]["residual"], "0")
        self.assertEqual(rows["minus_source_receiver"]["residual"], "0")
        self.assertIn("+ C(u,u)", rows["plus_receiver_minus_source"]["identity"])
        self.assertIn("- C(u,u)", rows["minus_source_receiver"]["identity"])

    def test_still_requires_source_map_and_residual_substitution(self) -> None:
        payload = build_payload()
        required = " ".join(payload["still_required"])

        self.assertTrue(payload["source_geodesic_required"])
        self.assertTrue(payload["same_phi_l_required"])
        self.assertTrue(payload["dl_b4vol_still_required"])
        self.assertFalse(payload["r_plus_r_minus_closed"])
        self.assertIn("same phi/L", required)
        self.assertIn("R_plus and R_minus", required)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Residuals zero: True", markdown)
        self.assertIn("R plus/R minus closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
