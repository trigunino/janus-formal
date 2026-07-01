from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_value_slip_scaffold import build_payload


class KiDS1000JanusHolstValueSlipScaffoldTests(unittest.TestCase):
    def test_scaffold_is_not_prediction_and_uses_no_kids_shortcuts(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "value-slip-scaffold-not-closed")
        self.assertFalse(payload["green_kernel_computed"])
        self.assertFalse(payload["uses_kids_residuals"])
        self.assertFalse(payload["uses_delta_z"])
        self.assertFalse(payload["uses_bin_factors"])
        self.assertFalse(payload["prediction_ready"])

    def test_scaffold_exposes_sigma_feed_interface(self) -> None:
        payload = build_payload()

        self.assertIn("Sigma_JH", payload["sigma_feed_formula"])
        self.assertEqual(len(payload["sample_derivative_source"]), 3)


if __name__ == "__main__":
    unittest.main()
