from __future__ import annotations

import unittest

from scripts.run_p0_eft_predrag_background_only_geff_scan import build_payload, grid


class P0EFTPredragBackgroundOnlyGeffScanTests(unittest.TestCase):
    def test_grid_contains_target_point(self) -> None:
        points = grid()

        self.assertTrue(any(point["label"] == "target_early" for point in points))

    def test_dry_payload(self) -> None:
        payload = build_payload(execute=False)

        self.assertEqual(payload["status"], "predrag-background-only-geff-scan-dry")
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
