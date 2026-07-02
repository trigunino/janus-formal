import unittest

from scripts.build_p0_eft_janus_z4_master_diagnostic_likelihood_trial_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticLikelihoodTrialGateTests(unittest.TestCase):
    def test_internal_trial_passes_without_observational_claim(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-likelihood-trial-gate")
        self.assertTrue(payload["likelihood_handshake_passed"])
        self.assertEqual(payload["trial_kind"], "internal_gr_reference_pseudo_likelihood")
        self.assertFalse(payload["uses_observed_planck_data"])
        self.assertFalse(payload["uses_official_planck_likelihood"])
        self.assertTrue(payload["diagnostic_likelihood_trial_passed"])
        self.assertTrue(payload["master_derived_signal_passed_carrier_projection"])
        self.assertTrue(payload["nonoverlap_accounting"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["observational_claim_allowed"])


if __name__ == "__main__":
    unittest.main()
