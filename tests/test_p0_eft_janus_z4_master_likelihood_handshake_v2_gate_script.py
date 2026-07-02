import unittest

from scripts.build_p0_eft_janus_z4_master_likelihood_handshake_v2_gate import build_payload


class P0EFTJanusZ4MasterLikelihoodHandshakeV2GateTests(unittest.TestCase):
    def test_v2_handshake_ready_but_likelihood_and_planck_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-likelihood-handshake-v2-gate")
        self.assertTrue(payload["action_normalization_v2_gate_passed"])
        self.assertTrue(payload["diagnostic_spectra_v2_generated"])
        self.assertTrue(payload["shape_v2_guards_passed"])
        self.assertTrue(payload["nonoverlap_accounting_basis_declared"])
        self.assertTrue(payload["carrier_threshold_passed"])
        self.assertTrue(payload["spectra_paths_exist"])
        self.assertTrue(payload["likelihood_handshake_v2_passed"])
        self.assertTrue(payload["diagnostic_likelihood_input_ready"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
