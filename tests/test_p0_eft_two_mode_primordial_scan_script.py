from __future__ import annotations

import unittest

from scripts.run_p0_eft_two_mode_primordial_scan import PRE_DRAG_GRID, VISIBILITY_GRID, build_payload


class P0EFTTwoModePrimordialScanTests(unittest.TestCase):
    def test_grid_contains_neutral_point(self) -> None:
        self.assertIn(0.0, PRE_DRAG_GRID)
        self.assertIn(0.0, VISIBILITY_GRID)

    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)
        self.assertEqual(payload["status"], "two-mode-primordial-scan-dry")
        self.assertEqual(payload["grid_size"], len(PRE_DRAG_GRID) * len(VISIBILITY_GRID))


if __name__ == "__main__":
    unittest.main()
