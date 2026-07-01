from __future__ import annotations

import unittest

from scripts.build_p0_eft_spin_background_projection import run_projection_scan


class P0EFTSpinBackgroundProjectionTests(unittest.TestCase):
    def test_projection_scan_runs(self) -> None:
        payload = run_projection_scan()

        self.assertEqual(payload["status"], "spin-background-projection-scan-computed")
        self.assertEqual(payload["xi_growth_locked"], 1.0)
        self.assertGreater(payload["valid_count"], 0)

    def test_best_branch_has_projection_coordinate(self) -> None:
        best = run_projection_scan()["best_total_chi2"]

        self.assertIn("xi_bg", best)
        self.assertGreaterEqual(best["xi_bg"], 0.0)
        self.assertLessEqual(best["xi_bg"], 1.0)


if __name__ == "__main__":
    unittest.main()
