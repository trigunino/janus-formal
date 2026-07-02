import unittest

from scripts.build_p0_eft_janus_z4_master_no_retuning_replay_gate import build_payload


class P0EFTJanusZ4MasterNoRetuningReplayGateTests(unittest.TestCase):
    def test_master_replay_is_fixed_and_does_not_unlock_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-no-retuning-replay-gate")
        self.assertTrue(payload["observed_planck_wrapper_handshake_gate_passed"])
        self.assertTrue(payload["normalization_fixed_to_a_sigma"])
        self.assertTrue(payload["baseline_spectra_exists"])
        self.assertTrue(payload["candidate_spectra_exists"])
        self.assertTrue(payload["carrier_threshold_passed"])
        self.assertFalse(payload["lambda_retuning_allowed"])
        self.assertFalse(payload["normalization_retuning_allowed"])
        self.assertFalse(payload["new_physics_channel_allowed"])
        self.assertTrue(payload["candidate_replayed_without_retuning"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
