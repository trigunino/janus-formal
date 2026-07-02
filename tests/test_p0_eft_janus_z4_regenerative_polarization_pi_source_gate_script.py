import unittest

from scripts.build_p0_eft_janus_z4_regenerative_polarization_pi_source_gate import build_payload


class P0EFTJanusZ4RegenerativePolarizationPiSourceGateTests(unittest.TestCase):
    def test_polarization_pi_source_regenerates_per_cosmology(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-regenerative-polarization-pi-source-gate")
        self.assertTrue(payload["lambda_frozen"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_new_physics"])
        self.assertTrue(payload["source_delta_cache_key_includes_cosmology_hash"])
        self.assertTrue(payload["source_delta_cache_key_includes_lambda_hash"])
        self.assertTrue(payload["hierarchy_lmax_included_in_cache_key"])
        self.assertTrue(payload["TCA_settings_hash_included_in_cache_key"])
        self.assertTrue(payload["opacity_grid_hash_included_in_cache_key"])
        self.assertTrue(payload["Theta_l_regenerated_per_cosmology"])
        self.assertTrue(payload["E_l_regenerated_per_cosmology"])
        self.assertTrue(payload["Pi_source_regenerated_per_cosmology"])
        self.assertTrue(payload["photon_polarization_hierarchy_regenerated_per_cosmology"])
        self.assertTrue(payload["Pi_source_derived_from_multipoles"])
        self.assertTrue(payload["no_free_Theta2_source_tag"])
        self.assertFalse(payload["direct_EE_patch"])
        self.assertFalse(payload["direct_TE_patch"])
        self.assertTrue(payload["no_stale_Pi_source_reuse"])
        self.assertTrue(payload["regenerative_polarization_pi_source_gate_passed"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
