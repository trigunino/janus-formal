import unittest

from scripts.build_p0_eft_janus_z4_two_sector_carrier_tangent_projection_gate import build_payload


class P0EFTJanusZ4TwoSectorCarrierTangentProjectionGateTests(unittest.TestCase):
    def test_two_sector_projection_classifies_before_spectra(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-carrier-tangent-projection-gate")
        self.assertTrue(payload["source_level_regeneration_gate_passed"])
        self.assertIn("full_two_sector", payload["projected_channels"])
        self.assertGreaterEqual(payload["parallel_fraction_full_two_sector"], 0.0)
        self.assertGreaterEqual(payload["perpendicular_fraction_full_two_sector"], 0.0)
        self.assertIn(payload["classification"], {"closure_recommended", "diagnostic_only", "candidate_path_possible"})
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertTrue(payload["rho_eff_shortcut_forbidden"])
        self.assertTrue(payload["direct_Cl_patch_forbidden"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
