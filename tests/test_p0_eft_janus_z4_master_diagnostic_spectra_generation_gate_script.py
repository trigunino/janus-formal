import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_diagnostic_spectra_generation_gate import build_payload


class P0EFTJanusZ4MasterDiagnosticSpectraGenerationGateTests(unittest.TestCase):
    def test_generates_internal_spectra_without_likelihood_unlock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-diagnostic-spectra-generation-gate")
        self.assertTrue(payload["diagnostic_spectra_readiness_gate_passed"])
        self.assertTrue(payload["diagnostic_spectra_generated"])
        self.assertTrue(Path(payload["baseline_spectra_path"]).exists())
        self.assertTrue(Path(payload["candidate_spectra_path"]).exists())
        self.assertTrue(payload["source_level_payload_replayed_after_serialization"])
        self.assertLess(payload["parallel_fraction_after_serialization"], 0.7)
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
