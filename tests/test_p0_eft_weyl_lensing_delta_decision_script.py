from __future__ import annotations

import unittest

from scripts.build_p0_eft_weyl_lensing_delta_decision import build_payload


class P0EFTWeylLensingDeltaDecisionTests(unittest.TestCase):
    def test_delta_window_found_but_lensing_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "weyl-lensing-delta-decision-recorded")
        self.assertTrue(payload["total_delta_window_found"])
        self.assertFalse(payload["strict_lensing_closed_at_best_total"])
        self.assertTrue(payload["balanced_window_found"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
