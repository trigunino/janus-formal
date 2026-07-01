from __future__ import annotations

import unittest

from scripts.run_p0_eft_lowe_tau_rescue_scan import TAU_GRID


class P0EFTLowETauRescueScanTests(unittest.TestCase):
    def test_tau_grid_is_ordered_and_bounded(self) -> None:
        self.assertGreater(len(TAU_GRID), 3)
        self.assertEqual(TAU_GRID, sorted(TAU_GRID))
        self.assertGreaterEqual(TAU_GRID[0], 0.0)
        self.assertLessEqual(TAU_GRID[-1], 0.1)


if __name__ == "__main__":
    unittest.main()
