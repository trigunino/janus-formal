from __future__ import annotations

import unittest

from scripts.run_p0_eft_polarization_source_shape_scan import POLARIZATION_SOURCE_GRID, build_payload


class P0EFTPolarizationSourceShapeScanTests(unittest.TestCase):
    def test_grid_contains_neutral_point(self) -> None:
        self.assertIn(0.0, POLARIZATION_SOURCE_GRID)
        self.assertEqual(POLARIZATION_SOURCE_GRID, sorted(POLARIZATION_SOURCE_GRID))

    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)
        self.assertEqual(payload["status"], "polarization-source-shape-scan-dry")
        self.assertEqual(payload["grid_size"], len(POLARIZATION_SOURCE_GRID))


if __name__ == "__main__":
    unittest.main()
