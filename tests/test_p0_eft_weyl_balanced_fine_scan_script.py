from __future__ import annotations

import unittest

from scripts.run_p0_eft_weyl_balanced_fine_scan import WEYL_FINE_GRID, build_fine_payload


class P0EFTWeylBalancedFineScanTests(unittest.TestCase):
    def test_grid_is_positive_and_contains_previous_best(self) -> None:
        self.assertIn(0.03, WEYL_FINE_GRID)
        self.assertTrue(all(value > 0 for value in WEYL_FINE_GRID))

    def test_dry_payload(self) -> None:
        payload = build_fine_payload(execute=False)
        self.assertEqual(payload["status"], "weyl-balanced-fine-scan-dry")
        self.assertEqual(payload["grid_size"], len(WEYL_FINE_GRID))


if __name__ == "__main__":
    unittest.main()
