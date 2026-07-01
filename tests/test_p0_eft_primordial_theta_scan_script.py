from __future__ import annotations

import unittest

from scripts.run_p0_eft_primordial_theta_scan import THETA_GRID, build_payload


class P0EFTPrimordialThetaScanTests(unittest.TestCase):
    def test_theta_grid_contains_neutral_point(self) -> None:
        self.assertIn(0.0, THETA_GRID)
        self.assertEqual(THETA_GRID, sorted(THETA_GRID))

    def test_dry_payload_is_well_formed(self) -> None:
        payload = build_payload(execute=False)

        self.assertEqual(payload["status"], "primordial-theta-scan-dry")
        self.assertEqual(payload["valid_points"], 0)
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
