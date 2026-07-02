import unittest

from scripts.build_p0_eft_janus_z4_master_observed_planck_diagnostic_trial_gate import build_payload


class P0EFTJanusZ4MasterObservedPlanckDiagnosticTrialGateTests(unittest.TestCase):
    def test_observed_trial_is_opt_in_and_non_promoting(self):
        payload = build_payload(run_observed=False)

        self.assertEqual(payload["status"], "janus-z4-master-observed-planck-diagnostic-trial-gate")
        self.assertTrue(payload["no_retuning_replay_gate_passed"])
        self.assertFalse(payload["run_observed_requested"])
        self.assertFalse(payload["run_observed_executed"])
        self.assertTrue(payload["diagnostic_trial_allowed"])
        self.assertTrue(payload["diagnostic_trial_passed"])
        self.assertTrue(payload["nonoverlap_accounting_required"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
