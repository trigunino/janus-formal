from __future__ import annotations

import unittest

from scripts.build_p0_eft_hubble_budget_stress_test import run_stress_tests


class P0EFTHubbleBudgetStressTestTests(unittest.TestCase):
    def test_stress_test_scores_variants(self) -> None:
        payload = run_stress_tests()

        self.assertEqual(payload["status"], "hubble-budget-stress-test-computed")
        self.assertGreater(len(payload["rows"]), 3)
        self.assertIn("best_total_chi2", payload)
        self.assertIn("best_radial_DH", payload)

    def test_baseline_and_spin_zero_are_present(self) -> None:
        names = {row["name"] for row in run_stress_tests()["rows"]}

        self.assertIn("baseline", names)
        self.assertIn("spin_zero", names)


if __name__ == "__main__":
    unittest.main()
