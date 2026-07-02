import unittest

from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_v2_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticShapeReportV2GateTests(unittest.TestCase):
    def test_v2_shape_report_is_diagnostic_and_nonoverlap_guarded(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-shape-report-v2-gate")
        self.assertTrue(payload["diagnostic_spectra_v2_gate_passed"])
        self.assertTrue(payload["shape_report_v2_generated"])
        self.assertTrue(payload["phase_guard_passed"])
        self.assertTrue(payload["amplitude_guard_passed"])
        self.assertTrue(payload["zero_artifact_guard_passed"])
        self.assertTrue(payload["nonoverlap_accounting_basis_declared"])
        self.assertTrue(payload["overlapping_sum_forbidden"])
        self.assertTrue(payload["reported_total_uses_one_highl_basis_only"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
