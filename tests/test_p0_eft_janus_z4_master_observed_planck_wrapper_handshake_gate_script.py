import unittest

from scripts.build_p0_eft_janus_z4_master_observed_planck_wrapper_handshake_gate import build_payload


class P0EFTJanusZ4MasterObservedPlanckWrapperHandshakeGateTests(unittest.TestCase):
    def test_observed_wrapper_gate_blocks_without_gr_same_wrapper_handshake(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-observed-planck-wrapper-handshake-gate")
        self.assertTrue(payload["official_likelihood_policy_declared"])
        self.assertFalse(payload["mock_wrappers_allowed"])
        self.assertFalse(payload["fallback_to_internal_pseudo_likelihood_allowed"])
        self.assertIn("highl_TTTEEE", payload["component_availability"])
        self.assertTrue(payload["observed_planck_wrapper_available"])
        self.assertFalse(payload["gr_reference_handshake_on_same_wrapper_passed"])
        self.assertFalse(payload["master_candidate_no_retuning_replay"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
