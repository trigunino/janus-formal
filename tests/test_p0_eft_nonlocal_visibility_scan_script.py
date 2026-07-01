from __future__ import annotations

import unittest

from scripts.run_p0_eft_nonlocal_visibility_scan import VISIBILITY_MEMORY_GRID, build_payload


class P0EFTNonlocalVisibilityScanTests(unittest.TestCase):
    def test_grid_contains_neutral_point(self) -> None:
        self.assertIn(0.0, VISIBILITY_MEMORY_GRID)
        self.assertEqual(VISIBILITY_MEMORY_GRID, sorted(VISIBILITY_MEMORY_GRID))

    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)
        self.assertEqual(payload["status"], "nonlocal-visibility-scan-dry")
        self.assertEqual(payload["grid_size"], len(VISIBILITY_MEMORY_GRID))


if __name__ == "__main__":
    unittest.main()
