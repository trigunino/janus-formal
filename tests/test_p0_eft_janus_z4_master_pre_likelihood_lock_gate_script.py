import unittest

from scripts.build_p0_eft_janus_z4_master_pre_likelihood_lock_gate import build_payload


class P0EFTJanusZ4MasterPreLikelihoodLockGateTests(unittest.TestCase):
    def test_lock_blocks_likelihood_when_shape_artifacts_exist(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-pre-likelihood-lock-gate")
        self.assertTrue(payload["shape_report_gate_passed"])
        self.assertTrue(payload["pre_likelihood_lock_active"])
        self.assertIn("cl_tt", payload["zero_crossing_artifacts"])
        self.assertIn("cl_ee", payload["zero_crossing_artifacts"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
