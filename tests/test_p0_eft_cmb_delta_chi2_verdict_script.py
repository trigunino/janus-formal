from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_delta_chi2_verdict import build_payload


class P0EFTCMBDeltaChi2VerdictTests(unittest.TestCase):
    def test_lowe_is_not_blocker_after_calibration(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-delta-chi2-verdict-recorded")
        self.assertFalse(payload["uses_lcdm_compressed_parameters_as_data"])
        self.assertTrue(payload["raw_planck_likelihood_used"])
        self.assertTrue(payload["lowE_reclassified_as_not_blocking"])

    def test_highl_and_lensing_are_residual_blockers(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["working_point_improves_total_delta_chi2"])
        self.assertFalse(payload["highl_reclassified_as_not_blocking_at_working_point"])
        self.assertTrue(payload["lensing_is_residual_blocker"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
