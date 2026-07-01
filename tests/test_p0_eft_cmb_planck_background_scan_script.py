from __future__ import annotations

import unittest
from pathlib import Path

from scripts.run_p0_eft_cmb_planck_background_scan import build_payload, grid, run_point


class P0EFTCMBPlanckBackgroundScanTests(unittest.TestCase):
    def test_grid_size(self) -> None:
        self.assertEqual(len(grid()), 128)

    def test_single_scan_point_runs(self) -> None:
        row = run_point(grid()[0])

        self.assertEqual(row["returncode"], 0)
        self.assertIsNotNone(row["chi2_CMB"])
        self.assertGreater(row["chi2_CMB"], 0.0)

    def test_limited_payload_writes_csv(self) -> None:
        payload = build_payload(limit=1)

        self.assertEqual(payload["grid_size"], 1)
        self.assertTrue(Path(payload["csv"]).exists())


if __name__ == "__main__":
    unittest.main()
