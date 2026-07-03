import unittest

from scripts.build_p0_eft_janus_z2_sigma_observational_roadmap_gate import build_payload


class P0EFTJanusZ2SigmaObservationalRoadmapGateTests(unittest.TestCase):
    def test_pure_math_closed_but_observational_model_is_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["z2_sigma_pure_math_closed"])
        self.assertTrue(payload["legacy_z4_archived"])
        self.assertTrue(payload["z4_physics_reactivation_forbidden"])
        self.assertTrue(payload["equation_locks"]["background_equations_derived"])
        self.assertTrue(payload["equation_locks"]["sigma_photon_geodesic_map_derived"])
        self.assertTrue(payload["equation_locks"]["bao_sound_ruler_formula_ready"])
        self.assertFalse(payload["equation_locks"]["bao_sound_ruler_evaluated"])
        self.assertTrue(payload["equation_locks"]["growth_perturbation_equations_derived"])
        self.assertTrue(payload["equation_locks"]["cmb_boltzmann_equations_derived"])
        self.assertTrue(payload["observation_equation_locks_closed"])
        self.assertFalse(payload["observation_prediction_inputs_ready"])
        self.assertNotIn("derive_z2_sigma_background_equations", payload["next_required"])
        self.assertNotIn("derive_sigma_photon_geodesic_distance_map", payload["next_required"])
        self.assertFalse(payload["non_compressed_observation_gates_passed"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertNotIn("derive_z2_sigma_cmb_boltzmann_equations", payload["next_required"])
        self.assertNotIn("derive_z2_sigma_growth_perturbation_equations", payload["next_required"])
        self.assertIn("evaluate_z2_sigma_bao_sound_ruler_without_fitted_rd", payload["next_required"])
        self.assertIn("reactivate_cyclic_z4_without_monodromy", payload["forbidden"])
        self.assertIn("use_planck_lcdm_compressed_parameters_as_validation", payload["forbidden"])


if __name__ == "__main__":
    unittest.main()
