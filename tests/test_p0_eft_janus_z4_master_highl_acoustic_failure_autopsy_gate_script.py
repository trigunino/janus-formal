import unittest

from scripts.build_p0_eft_janus_z4_master_highl_acoustic_failure_autopsy_gate import build_payload


class P0EFTJanusZ4MasterHighLAcousticFailureAutopsyGateTests(unittest.TestCase):
    def test_autopsy_localizes_failure_without_promotion_or_retuning(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-highl-acoustic-failure-autopsy-gate")
        self.assertTrue(payload["observed_failure_map_v2_rejected"])
        self.assertEqual(payload["observed_failure_class"], "high_l_acoustic_shape_failure")
        self.assertIn(payload["failure_subclass"], {
            "acoustic_phase_failure",
            "damping_tail_or_high_l_shape_failure",
            "acoustic_driving_or_baryon_loading_failure",
            "likelihood_weighted_high_l_failure",
        })
        self.assertEqual(len(payload["tt_peak_diagnostics"]), 3)
        self.assertEqual(len(payload["te_zero_diagnostics"]), 3)
        self.assertEqual(len(payload["ee_peak_diagnostics"]), 3)
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["new_physics_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        self.assertFalse(payload["planck_retry_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
