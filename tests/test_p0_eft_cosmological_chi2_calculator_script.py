from __future__ import annotations

import unittest

from scripts.build_p0_eft_cosmological_chi2_calculator import build_payload


class P0EFTCosmologicalChi2CalculatorTests(unittest.TestCase):
    def test_chi2_payload_is_computed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sdss-chi2-computed")
        self.assertGreater(payload["data_points"], 0)
        self.assertGreater(payload["chi2_best_amplitude"], 0)
        self.assertTrue(payload["full_covariance_used"])
        self.assertGreater(payload["chi2_best_amplitude_full_covariance"], 0)

    def test_residuals_have_pulls(self) -> None:
        payload = build_payload()

        self.assertTrue(all("pull" in row for row in payload["residuals"]))
        self.assertEqual(len(payload["residuals"]), payload["data_points"])

    def test_full_covariance_changes_diagonal_score(self) -> None:
        payload = build_payload()

        self.assertNotEqual(
            payload["chi2_unit_amplitude"],
            payload["chi2_unit_amplitude_full_covariance"],
        )


if __name__ == "__main__":
    unittest.main()
