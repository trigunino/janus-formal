import unittest

from scripts.build_p0_eft_janus_z4_two_sector_stability_eigenmode_gate import build_payload


class P0EFTJanusZ4TwoSectorStabilityEigenmodeGateTests(unittest.TestCase):
    def test_stability_eigenmode_gate_allows_source_regen_not_spectra(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-stability-eigenmode-gate")
        self.assertTrue(payload["linear_evolution_gate_passed"])
        self.assertTrue(payload["eigenvalues_finite"])
        self.assertTrue(payload["no_explosive_real_modes"])
        self.assertTrue(payload["superhorizon_k_regular"])
        self.assertTrue(payload["subhorizon_k_regular"])
        self.assertTrue(payload["symmetric_mode_stable"])
        self.assertTrue(payload["antisymmetric_Z4_mode_stable"])
        self.assertTrue(payload["relative_isocurvature_mode_stable"])
        self.assertTrue(payload["projection_mode_stable"])
        self.assertTrue(payload["ghost_tachyon_guard"])
        self.assertTrue(payload["constraint_preservation_guard"])
        self.assertTrue(payload["GR_limit_stability_recovered"])
        self.assertTrue(payload["source_level_regeneration_allowed"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["carrier_tangent_projection_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
