import unittest

from scripts.build_p0_eft_janus_z4_master_diagnostic_likelihood_trial_v2_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticLikelihoodTrialV2GateTests(unittest.TestCase):
    def test_v2_internal_trial_passes_without_observational_claim(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-likelihood-trial-v2-gate")
        self.assertTrue(payload["likelihood_handshake_v2_passed"])
        self.assertEqual(payload["trial_kind"], "internal_gr_reference_pseudo_likelihood_v2")
        self.assertFalse(payload["uses_observed_planck_data"])
        self.assertFalse(payload["uses_official_planck_likelihood"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertTrue(payload["diagnostic_likelihood_trial_v2_passed"])
        self.assertTrue(payload["master_derived_signal_passed_carrier_projection"])
        self.assertTrue(payload["nonoverlap_accounting"])
        self.assertTrue(payload["overlapping_sum_forbidden"])
        self.assertGreater(payload["pseudo_chi2_total_combined_highl"], 0.0)
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
