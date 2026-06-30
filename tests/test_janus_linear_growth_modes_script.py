from __future__ import annotations

import unittest

from scripts.build_janus_linear_growth_modes import build_payload


class JanusLinearGrowthModesTests(unittest.TestCase):
    def test_modes_are_sum_and_signed_contrast(self) -> None:
        payload = build_payload()
        modes = {row["mode"]: row for row in payload["basis"]}

        self.assertFalse(payload["physics_closed"])
        self.assertIn("sum_mode", modes)
        self.assertIn("signed_contrast_mode", modes)
        self.assertIn("Omega_minus", modes["sum_mode"]["definition"])
        self.assertIn("delta_null''", modes["sum_mode"]["equation"])
        self.assertIn("lambda_source", modes["signed_contrast_mode"]["equation"])

    def test_no_fit_rules_block_sigma8_and_lcdm_transfer(self) -> None:
        payload = build_payload()
        rules = " ".join(payload["no_fit_rules"])
        inputs = " ".join(payload["operator_inputs"])

        self.assertIn("sigma8", rules)
        self.assertIn("Lambda-CDM", rules)
        self.assertIn("Q_det", inputs)
        self.assertIn("Omega_plus", inputs)


if __name__ == "__main__":
    unittest.main()
