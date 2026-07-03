import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_stress_extraction_gate import build_payload


class P0EFTJanusZ2SigmaBoundaryStressExtractionGateTests(unittest.TestCase):
    def test_boundary_stress_formula_is_closed_from_sigma_action(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["formula"]["full_boundary_action_closed_on_sigma"])
        self.assertTrue(payload["formula"]["T_eff_ab_extraction_formula_ready"])
        self.assertTrue(payload["boundary_stress_extraction_formula_closed"])
        self.assertIn("T_CartanGHY_ab", payload["component_blocks"])

    def test_component_reduction_is_still_required_for_flrw_projection(self):
        payload = build_payload()

        self.assertFalse(payload["reduction"]["T_eff_ab_component_reduction_ready"])
        self.assertFalse(payload["reduction"]["T_eff_ab_ready_for_FLRW_projection"])
        self.assertFalse(payload["boundary_stress_ready_for_FLRW"])
        self.assertIn("reduce_each_T_eff_ab_component_on_FLRW_induced_metric", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
