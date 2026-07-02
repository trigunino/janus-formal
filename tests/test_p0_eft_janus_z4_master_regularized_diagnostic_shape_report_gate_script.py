import unittest

from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_shape_report_gate import build_payload


class P0EFTJanusZ4MasterRegularizedDiagnosticShapeReportGateTests(unittest.TestCase):
    def test_regularized_shape_report_clears_shape_lock_but_not_planck_lock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-regularized-diagnostic-shape-report-gate")
        self.assertTrue(payload["regularized_diagnostic_spectra_generation_gate_passed"])
        self.assertTrue(payload["regularized_shape_report_generated"])
        self.assertEqual(payload["zero_crossing_artifacts"], {})
        self.assertFalse(payload["pre_likelihood_shape_lock_active"])
        self.assertFalse(payload["full_upstream_action_derived"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
