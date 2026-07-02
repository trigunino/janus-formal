import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_source_component_diagnostic_spectra_gate import build_payload


class P0EFTJanusZ4MasterSourceComponentDiagnosticSpectraGateTests(unittest.TestCase):
    def test_component_spectra_are_diagnostic_only(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-source-component-diagnostic-spectra-gate")
        self.assertTrue(payload["source_component_attribution_complete"])
        self.assertFalse(payload["unlensed_lensed_split_available"])
        self.assertFalse(payload["observed_likelihood_allowed"])
        self.assertFalse(payload["planck_retry_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["new_physics_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        for path in payload["component_spectra_paths"].values():
            self.assertTrue(Path(path).exists())


if __name__ == "__main__":
    unittest.main()
