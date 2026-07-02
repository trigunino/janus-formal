import unittest

from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_readiness_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticSpectraReadinessGateTests(unittest.TestCase):
    def test_readiness_allows_only_internal_diagnostic_spectra(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-spectra-readiness-gate")
        self.assertTrue(payload["master_source_carrier_tangent_replay_passed"])
        self.assertTrue(payload["constraint_closure_audit_passed"])
        self.assertTrue(payload["diagnostic_spectra_generation_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["lambda_retuning_allowed"])
        self.assertIn("write_internal_GR_plus_master_delta_spectra", payload["diagnostic_scope"])
        self.assertIn("Planck_likelihood", payload["forbidden_scope"])


if __name__ == "__main__":
    unittest.main()
