import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_regularized_diagnostic_spectra_v2_gate import build_payload


class P0EFTJanusZ4MasterRegularizedDiagnosticSpectraV2GateTests(unittest.TestCase):
    def test_generates_v2_diagnostic_spectra_without_likelihood_unlock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-regularized-diagnostic-spectra-v2-gate")
        self.assertTrue(payload["revised_carrier_tangent_projection_passed"])
        self.assertTrue(payload["diagnostic_spectra_v2_generated"])
        self.assertTrue(Path(payload["baseline_spectra_path"]).exists())
        self.assertTrue(Path(payload["candidate_spectra_path"]).exists())
        self.assertLess(payload["parallel_fraction_after_serialization"], 0.7)
        self.assertFalse(payload["official_planck_trial_allowed"])
        self.assertFalse(payload["likelihood_evaluation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
