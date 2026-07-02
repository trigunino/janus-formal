import unittest

from scripts.build_p0_eft_janus_z4_planck_likelihood_completeness_gate import build_payload


class P0EFTJanusZ4PlanckLikelihoodCompletenessGateTests(unittest.TestCase):
    def test_likelihood_completeness_gate(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-planck-likelihood-completeness-gate")
        self.assertTrue(payload["candidate_state_checkpoint_created"])
        self.assertTrue(payload["highl_TT_available"])
        self.assertTrue(payload["highl_TTTEEE_available"])
        self.assertTrue(payload["highl_TE_standalone_available"])
        self.assertTrue(payload["highl_EE_standalone_available"])
        self.assertTrue(payload["local_highl_TE_standalone_clik_available"])
        self.assertTrue(payload["local_highl_EE_standalone_clik_available"])
        self.assertTrue(payload["low_l_TT_available"])
        self.assertTrue(payload["low_l_EE_available"])
        self.assertTrue(payload["lensing_available"])
        self.assertTrue(payload["standalone_highl_TE_EE_available"])
        self.assertTrue(payload["candidate_trial_allowed"])
        self.assertFalse(payload["full_planck_validation_allowed"])
        self.assertTrue(payload["generated_outputs_not_imported_as_sources"])
        self.assertTrue(payload["planck_likelihood_completeness_gate_passed"])


if __name__ == "__main__":
    unittest.main()
