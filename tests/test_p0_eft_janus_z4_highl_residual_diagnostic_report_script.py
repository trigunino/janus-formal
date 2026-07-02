import unittest

from scripts.build_p0_eft_janus_z4_highl_residual_diagnostic_report import build_payload


class P0EFTJanusZ4HighLResidualDiagnosticReportTests(unittest.TestCase):
    def test_residual_report(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-highl-residual-diagnostic-report")
        self.assertTrue(payload["residual_report_complete"])
        self.assertIn("TT", payload["band_residuals"])
        self.assertIn("TE", payload["band_residuals"])
        self.assertIn("EE", payload["band_residuals"])
        self.assertIn("combined_highl", payload["nonoverlap_accounting"])
        self.assertIn("decomposed_highl", payload["nonoverlap_accounting"])
        self.assertIn("legacy_overlapping_total_diagnostic_only", payload["nonoverlap_accounting"])


if __name__ == "__main__":
    unittest.main()
