import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_source_level_regeneration_gate import build_payload


class P0EFTJanusZ4DerivedSlipSourceLevelRegenerationGateTests(unittest.TestCase):
    def test_source_level_regeneration_reconstructs_potentials_with_slip(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-source-level-regeneration-gate")
        self.assertTrue(payload["deltaSlip_Z4_value_available"])
        self.assertTrue(payload["deltaSlip_Z4_dot_available"])
        self.assertTrue(payload["visible_slip_projection_declared"])
        self.assertTrue(payload["Dirichlet_boundary_value_zero_logged"])
        self.assertTrue(payload["normal_derivative_projection_nonzero_logged"])
        self.assertTrue(payload["normal_orientation_sign_declared"])
        self.assertIn(payload["normal_orientation_sign"], (-1.0, 1.0))
        self.assertTrue(payload["source_level_cache_key_includes_slip_kernel_hash"])
        self.assertTrue(payload["deltaPhi_Z4_reconstructed"])
        self.assertTrue(payload["deltaPsi_Z4_reconstructed"])
        self.assertTrue(payload["temperature_surface_term_regenerated_with_slip"])
        self.assertTrue(payload["temperature_early_ISW_term_regenerated_with_slip"])
        self.assertTrue(payload["temperature_source_regenerated_with_slip"])
        self.assertTrue(payload["Pi_source_regenerated_with_slip"])
        self.assertTrue(payload["photon_polarization_hierarchy_regenerated_with_slip"])
        self.assertTrue(payload["full_slip_source_regenerated"])
        self.assertGreater(payload["surface_term_norm"], 0.0)
        self.assertGreater(payload["early_ISW_term_norm"], 0.0)
        self.assertGreater(payload["Pi_source_norm"], 0.0)
        self.assertTrue(payload["GR_limit_slip_zero"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertTrue(payload["derived_slip_source_level_regeneration_gate_passed"])
        self.assertFalse(payload["local_cosmology_profiling_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
