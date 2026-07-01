from __future__ import annotations

import unittest
from pathlib import Path

from scripts.run_p0_eft_cmb_planck_mini_scan import grid, run_point


class P0EFTCMBPlanckMiniScanTests(unittest.TestCase):
    def test_planck_mini_scan_runs(self) -> None:
        points = grid()

        self.assertEqual(len(points), 54)
        self.assertTrue(Path("outputs/reports/p0_eft_cmb_planck_mini_scan.csv").exists())

    def test_best_chi2_is_recorded(self) -> None:
        row = run_point({"As": 2.1e-9, "ns": 0.94, "tau": 0.035, "nnu": 3.7424238})

        self.assertEqual(row["returncode"], 0)
        self.assertIsNotNone(row["chi2_CMB"])
        self.assertGreater(row["chi2_CMB"], 0.0)


if __name__ == "__main__":
    unittest.main()
