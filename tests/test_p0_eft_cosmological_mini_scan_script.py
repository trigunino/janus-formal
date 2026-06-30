from __future__ import annotations

import unittest

from scripts.run_p0_eft_cosmological_mini_scan import run_scan


class P0EFTCosmologicalMiniScanTests(unittest.TestCase):
    def test_scan_computes_best_rows(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "mini-scan-computed")
        self.assertGreater(payload["physical_count"], 0)
        self.assertIsNotNone(payload["best_unit_amplitude"])
        self.assertIsNotNone(payload["best_free_amplitude"])

    def test_best_rows_have_chi2(self) -> None:
        payload = run_scan()

        self.assertIn("chi2_unit", payload["best_unit_amplitude"])
        self.assertIn("chi2_best", payload["best_free_amplitude"])


if __name__ == "__main__":
    unittest.main()
