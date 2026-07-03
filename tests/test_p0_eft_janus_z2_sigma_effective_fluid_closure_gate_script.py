import unittest

from scripts.build_p0_eft_janus_z2_sigma_effective_fluid_closure_gate import build_payload


class P0EFTJanusZ2SigmaEffectiveFluidClosureGateTests(unittest.TestCase):
    def test_bibliography_supports_method_but_not_direct_janus_formula(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography"]["israel_junction_conditions_checked"])
        self.assertTrue(payload["bibliography"]["brown_york_stress_tensor_checked"])
        self.assertTrue(payload["bibliography"]["cosmological_thin_shell_fluid_checked"])
        self.assertFalse(payload["bibliography"]["direct_janus_z2_sigma_rho_p_formula_found"])

    def test_structural_projection_is_ready_but_numeric_fluid_is_not(self):
        payload = build_payload()

        self.assertTrue(payload["effective_fluid_structural_projection_ready"])
        self.assertTrue(payload["structural"]["T_eff_ab_extraction_formula_ready"])
        self.assertFalse(payload["structural"]["T_eff_ab_ready_for_FLRW_projection"])
        self.assertFalse(payload["numeric"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["numeric"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["effective_fluid_numeric_closure_ready"])
        self.assertIn("reduce_rho_eff_and_p_eff_to_functions_of_scale_factor", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
