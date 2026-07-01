from __future__ import annotations

import unittest

from scripts.run_p0_eft_immirzi_patch_mini_scan import build_payload, grid


class P0EFTImmirziPatchMiniScanTests(unittest.TestCase):
    def test_grid_is_small_and_structured(self) -> None:
        points = grid()

        self.assertEqual(len(points), 12)
        self.assertIn({"delta_i": 0.06, "width": 0.0002}, points)

    def test_dry_payload_does_not_claim_acceptance(self) -> None:
        payload = build_payload(points=[{"delta_i": 0.03, "width": 0.0001}], execute=False)

        self.assertEqual(payload["status"], "immirzi-patch-mini-scan-dry")
        self.assertFalse(payload["planck_accepted"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
