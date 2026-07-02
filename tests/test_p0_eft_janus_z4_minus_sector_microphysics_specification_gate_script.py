import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_microphysics_specification_gate import build_payload


class P0EFTJanusZ4MinusSectorMicrophysicsSpecificationGateTests(unittest.TestCase):
    def test_microphysics_specification_blocks_shortcuts(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-microphysics-specification-gate")
        self.assertTrue(payload["previous_minus_transfer_rank1_diagnosis"])
        self.assertIn("sound_speed_or_jeans_scale", payload["required_non_amplitude_microphysics"])
        self.assertEqual(payload["first_test_route"], "sound_speed_jeans")
        self.assertFalse(payload["minus_sector_amplitude_knob_allowed"])
        self.assertFalse(payload["rho_eff_shortcut_allowed"])
        self.assertFalse(payload["projection_only_fix_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])


if __name__ == "__main__":
    unittest.main()
