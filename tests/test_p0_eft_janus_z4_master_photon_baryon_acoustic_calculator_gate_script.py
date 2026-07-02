import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_master_photon_baryon_acoustic_calculator_gate import build_payload


class P0EFTJanusZ4MasterPhotonBaryonAcousticCalculatorGateTests(unittest.TestCase):
    def test_acoustic_calculator_is_diagnostic_and_blocks_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-master-photon-baryon-acoustic-calculator-gate")
        self.assertTrue(payload["input_requires_rederivation"])
        self.assertTrue(payload["oscillator_phase_declared"])
        self.assertTrue(payload["doppler_quadrature_declared"])
        self.assertTrue(payload["calculator_diagnostic_ready"])
        self.assertTrue(Path(payload["calculator_payload_path"]).exists())
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["observed_likelihood_allowed"])
        self.assertFalse(payload["planck_retry_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["retuning_allowed"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
