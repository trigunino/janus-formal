from __future__ import annotations

import unittest

from scripts.run_p0_eft_screened_rd_cmb_projection_scan import build_payload


class P0EFTScreenedRdCMBProjectionScanTests(unittest.TestCase):
    def test_dry_payload_has_screening_grid(self) -> None:
        payload = build_payload(execute=False)

        self.assertEqual(payload["status"], "screened-rd-cmb-projection-scan-dry")
        self.assertGreater(len(payload["points"]), 3)
        self.assertLess(payload["rd_ratio_background"], 0.96)
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
