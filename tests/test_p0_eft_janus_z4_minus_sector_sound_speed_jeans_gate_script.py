import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_sound_speed_jeans_gate import build_payload


class P0EFTJanusZ4MinusSectorSoundSpeedJeansGateTests(unittest.TestCase):
    def test_sound_speed_jeans_gate_reports_pre_observational_status(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-sound-speed-jeans-gate")
        self.assertEqual(payload["microphysics_route"], "sound_speed_jeans")
        self.assertFalse(payload["is_derived_from_full_action"])
        self.assertFalse(payload["free_minus_amplitude_allowed"])
        rows = payload["transfer_rows"]
        for name in ("density", "velocity", "shear", "Weyl", "Theta0", "Pi", "projection_source"):
            self.assertIn(name, rows)
            self.assertIn("residual_after_best_amplitude_fit", rows[name])
            self.assertIn("effective_transfer_rank", rows[name])
            self.assertIn("parallel_fraction", rows[name])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
