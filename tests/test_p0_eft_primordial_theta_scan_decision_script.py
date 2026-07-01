from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_theta_scan_decision import build_payload


class P0EFTPrimordialThetaScanDecisionTests(unittest.TestCase):
    def test_single_mode_branch_is_excluded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-theta-scan-decision-recorded")
        self.assertTrue(payload["neutral_theta_is_best"])
        self.assertFalse(payload["nonzero_theta_improves_planck"])
        self.assertTrue(payload["ward_single_mode_branch_excluded"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
