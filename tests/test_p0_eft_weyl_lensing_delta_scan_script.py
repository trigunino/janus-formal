from __future__ import annotations

import unittest

from scripts.run_p0_eft_weyl_lensing_delta_scan import LENSING_GRID, WEYL_GRID, build_payload


class P0EFTWeylLensingDeltaScanTests(unittest.TestCase):
    def test_grid_contains_neutral_point(self) -> None:
        self.assertIn(0.0, WEYL_GRID)
        self.assertIn(0.0, LENSING_GRID)

    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)
        self.assertEqual(payload["status"], "weyl-lensing-delta-scan-dry")
        self.assertEqual(payload["grid_size"], len(WEYL_GRID) * len(LENSING_GRID))


if __name__ == "__main__":
    unittest.main()
