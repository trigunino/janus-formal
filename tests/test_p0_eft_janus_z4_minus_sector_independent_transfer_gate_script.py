import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_independent_transfer_gate import build_payload


class P0EFTJanusZ4MinusSectorIndependentTransferGateTests(unittest.TestCase):
    def test_minus_transfer_gate_reports_no_observational_unlock(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-independent-transfer-gate")
        rows = payload["transfer_rows"]
        for name in ("density", "velocity", "shear", "Weyl", "Theta0", "Pi", "projection_source"):
            self.assertIn(name, rows)
            self.assertIn("minus_over_plus_amplitude_fit", rows[name])
            self.assertIn("residual_after_best_amplitude_fit", rows[name])
            self.assertIn("effective_transfer_rank", rows[name])
            self.assertIn("minus_sector_independent_transfer", rows[name])
        self.assertIsInstance(payload["independent_transfer_components"], list)
        self.assertTrue(payload["no_rho_eff_shortcut"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["projection_retuning_allowed"])
        self.assertFalse(payload["free_minus_amplitude_allowed"])
        self.assertFalse(payload["hidden_rescaling_coefficient_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
