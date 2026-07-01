from __future__ import annotations

import unittest

from scripts.run_p0_eft_screened_geff_camb_gate import build_payload


class P0EFTScreenedGeffCAMBGateTests(unittest.TestCase):
    def test_dry_payload_splits_background_and_cmb_couplings(self) -> None:
        payload = build_payload(execute=False)
        point = payload["point"]

        self.assertEqual(payload["status"], "screened-geff-camb-gate-dry")
        self.assertLess(point["c_cmb"], point["c_background"])
        self.assertAlmostEqual(point["c_cmb"], 0.1 * point["c_background"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
