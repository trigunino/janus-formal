import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_thermal_ratio_gate import build_payload


class P0EFTJanusZ4MinusSectorThermalRatioGateTests(unittest.TestCase):
    def test_thermal_ratio_gate_blocks_observational_use(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-thermal-ratio-gate")
        self.assertEqual(payload["microphysics_route"], "thermal_ratio")
        self.assertFalse(payload["is_derived_from_full_action"])
        self.assertFalse(payload["free_thermal_ratio_fit_allowed"])
        rows = payload["transfer_rows"]
        for name in ("thermal_density", "pressure_law", "damping_scale", "decoupling_timing_proxy", "Pi_response", "full_channel"):
            self.assertIn(name, rows)
            self.assertIn("effective_transfer_rank", rows[name])
            self.assertIn("parallel_fraction", rows[name])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
