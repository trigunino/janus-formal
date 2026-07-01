from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_lowe_sector_gate import ACCEPTANCE_CHI2, build_payload


class P0EFTPrimordialLowESectorGateTests(unittest.TestCase):
    def test_lowe_only_is_excluded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-lowe-sector-gate-recorded")
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertTrue(payload["reionization_lowE_only_excluded"])
        self.assertTrue(payload["highl_only_excluded"])
        self.assertTrue(payload["requires_combined_primordial_highl_and_lowE_sector"])

    def test_highl_dominates_even_with_perfect_lowe(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["chi2_if_lowE_EE_were_perfect"], ACCEPTANCE_CHI2)
        self.assertGreater(payload["chi2_if_highl_were_perfect"], ACCEPTANCE_CHI2)
        self.assertGreater(payload["highl_fraction_of_chi2"], 0.5)
        self.assertLess(payload["lowE_EE_fraction_of_chi2"], 0.1)


if __name__ == "__main__":
    unittest.main()
