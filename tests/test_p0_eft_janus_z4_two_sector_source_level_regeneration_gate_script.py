import unittest

from scripts.build_p0_eft_janus_z4_two_sector_source_level_regeneration_gate import build_payload


class P0EFTJanusZ4TwoSectorSourceLevelRegenerationGateTests(unittest.TestCase):
    def test_source_level_regenerates_two_sector_sources_without_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-source-level-regeneration-gate")
        self.assertTrue(payload["stability_gate_passed"])
        self.assertTrue(payload["plus_source_regenerated"])
        self.assertTrue(payload["minus_source_regenerated"])
        self.assertTrue(payload["antisymmetric_Z4_source_regenerated"])
        self.assertTrue(payload["projection_source_regenerated"])
        self.assertTrue(payload["deltaWeyl_plus_observable_regenerated"])
        self.assertTrue(payload["Theta0_two_sector_projection_regenerated"])
        self.assertTrue(payload["Pi_two_sector_projection_regenerated"])
        self.assertTrue(payload["source_cache_key_includes_two_sector_version"])
        self.assertTrue(payload["source_cache_key_includes_projection_hash"])
        self.assertTrue(payload["source_cache_key_includes_mode_basis_hash"])
        self.assertTrue(payload["rho_eff_shortcut_forbidden"])
        self.assertTrue(payload["direct_Cl_patch_forbidden"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertTrue(payload["carrier_tangent_projection_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
