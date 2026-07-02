import unittest

from scripts.build_p0_eft_janus_z4_master_official_likelihood_policy_v2_gate import build_payload


class P0EFTJanusZ4MasterOfficialLikelihoodPolicyV2GateTests(unittest.TestCase):
    def test_v2_policy_blocks_official_planck_after_internal_trial(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-official-likelihood-policy-v2-gate")
        self.assertTrue(payload["diagnostic_likelihood_trial_v2_passed"])
        self.assertTrue(payload["official_likelihood_policy_declared"])
        self.assertFalse(payload["diagnostic_trial_uses_observed_planck_data"])
        self.assertFalse(payload["diagnostic_trial_uses_official_planck_likelihood"])
        self.assertIn("GR_reference_handshake_on_same_wrapper_v2", payload["required_before_official_planck"])
        self.assertFalse(payload["observed_planck_wrapper_declared"])
        self.assertFalse(payload["gr_reference_handshake_on_same_wrapper"])
        self.assertFalse(payload["master_v2_no_retuning_replay"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
