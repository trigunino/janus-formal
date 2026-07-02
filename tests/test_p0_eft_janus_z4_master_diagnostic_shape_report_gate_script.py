import unittest

from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticShapeReportGateTests(unittest.TestCase):
    def test_shape_report_is_diagnostic_only(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-shape-report-gate")
        self.assertTrue(payload["diagnostic_spectra_generation_gate_passed"])
        self.assertTrue(payload["shape_report_generated"])
        for channel in ("cl_tt", "cl_te", "cl_ee"):
            self.assertIn(channel, payload["shape_rows"])
            self.assertIn("max_abs_fractional_deviation", payload["shape_rows"][channel])
            self.assertIn("peak_shift", payload["shape_rows"][channel])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
