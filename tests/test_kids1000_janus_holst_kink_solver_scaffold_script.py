from __future__ import annotations

import unittest

from scripts.build_kids1000_janus_holst_kink_solver_scaffold import build_payload


class KiDS1000JanusHolstKinkSolverScaffoldTests(unittest.TestCase):
    def test_payload_blocks_prediction_without_source_coefficients(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "kink-growth-solver-scaffold-not-predictive")
        self.assertFalse(payload["skink_coefficient_derived"])
        self.assertFalse(payload["alpha_Janus_derived"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["uses_kids_residuals"])
        self.assertFalse(payload["uses_bin_shift"])
        self.assertFalse(payload["uses_bin_factors"])

    def test_payload_shows_jump_mechanics(self) -> None:
        check = build_payload()["mechanics_check"]

        self.assertTrue(check["delta_continuity_encoded"])
        self.assertTrue(check["growth_velocity_jump_encoded"])
        self.assertGreater(check["enabled_mechanics_final_ddelta"], check["disabled_final_ddelta"])


if __name__ == "__main__":
    unittest.main()
