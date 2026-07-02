import unittest

from scripts.build_p0_eft_janus_z4_minus_sector_shear_free_streaming_gate import build_payload


class P0EFTJanusZ4MinusSectorShearFreeStreamingGateTests(unittest.TestCase):
    def test_shear_free_streaming_gate_is_pre_observational(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-minus-sector-shear-free-streaming-gate")
        self.assertEqual(payload["microphysics_route"], "shear_free_streaming")
        self.assertFalse(payload["is_derived_from_full_action"])
        self.assertTrue(payload["sigma_minus_declared"])
        self.assertTrue(payload["F_l_minus_hierarchy_declared"])
        rows = payload["transfer_rows"]
        for name in ("shear_only", "free_streaming_only", "Weyl_anisotropic_stress", "Pi_response", "full_channel"):
            self.assertIn(name, rows)
            self.assertIn("effective_transfer_rank", rows[name])
            self.assertIn("parallel_fraction", rows[name])
        self.assertFalse(payload["free_shear_amplitude_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])


if __name__ == "__main__":
    unittest.main()
