import unittest

from scripts.build_p0_eft_janus_z2_sigma_flrw_boundary_stress_reduction_gate import build_payload


class P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGateTests(unittest.TestCase):
    def test_setup_is_declared_from_closed_boundary_stress(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["setup"]["boundary_stress_extraction_formula_closed"])
        self.assertTrue(payload["setup"]["induced_FLRW_sigma_metric_declared"])
        self.assertTrue(payload["setup"]["Z2_normal_orientation_declared"])

    def test_component_reductions_remain_blocking(self):
        payload = build_payload()

        self.assertTrue(payload["component_reductions"]["cartan_GHY_FLRW_reduced"])
        self.assertFalse(payload["all_component_reductions_ready"])
        self.assertFalse(payload["flrw_boundary_stress_reduction_ready"])
        self.assertFalse(payload["projection"]["T_eff_ab_ready_for_FLRW_projection"])
        self.assertIn("holst_Nieh_Yan_FLRW_reduced", payload["blocked_components"])
        self.assertIn("fix_component_signs_from_Z2_normal_orientation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
