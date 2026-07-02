import unittest

from scripts.build_p0_eft_janus_z4_master_pre_likelihood_lock_v2_gate import build_payload


class P0EFTJanusZ4MasterPreLikelihoodLockV2GateTests(unittest.TestCase):
    def test_v2_lock_clears_only_likelihood_handshake_not_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-pre-likelihood-lock-v2-gate")
        self.assertTrue(payload["shape_report_v2_gate_passed"])
        self.assertFalse(payload["pre_likelihood_lock_active"])
        self.assertTrue(payload["pre_likelihood_lock_cleared"])
        self.assertEqual(payload["lock_reasons"], [])
        self.assertTrue(payload["phase_guard_passed"])
        self.assertTrue(payload["amplitude_guard_passed"])
        self.assertTrue(payload["zero_artifact_guard_passed"])
        self.assertTrue(payload["nonoverlap_accounting_basis_declared"])
        self.assertTrue(payload["likelihood_handshake_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
