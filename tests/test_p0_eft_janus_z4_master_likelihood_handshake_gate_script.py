import unittest

from scripts.build_p0_eft_janus_z4_master_likelihood_handshake_gate import build_payload


class P0EFTJanusZ4MasterLikelihoodHandshakeGateTests(unittest.TestCase):
    def test_handshake_ready_but_official_planck_still_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-likelihood-handshake-gate")
        self.assertTrue(payload["action_normalization_gate_passed"])
        self.assertTrue(payload["regularized_diagnostic_spectra_generated"])
        self.assertTrue(payload["regularized_shape_lock_cleared"])
        self.assertTrue(payload["carrier_threshold_passed"])
        self.assertTrue(payload["spectra_paths_exist"])
        self.assertTrue(payload["likelihood_handshake_passed"])
        self.assertTrue(payload["diagnostic_likelihood_input_ready"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
