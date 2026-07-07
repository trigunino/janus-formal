import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_spectral_bridge_matrix import build_payload


class ChiLLSpectralBridgeMatrixTests(unittest.TestCase):
    def test_spectral_scale_does_not_unblock_routes_alone(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["chi_LL_prediction_ready"])
        self.assertEqual(payload["routes_unblocked_by_spectral_scale_alone"], [])

    def test_casimir_and_spin_receive_specific_help(self):
        bridges = build_payload()["bridges"]

        self.assertIn("power_law_Rs_dependence", bridges["Casimir_topological_exit"]["newly_calculable"])
        self.assertIn("level_spacing_scale_1_over_Rs", bridges["spin_condensate_exit"]["newly_calculable"])

    def test_best_combined_routes_are_reported(self):
        routes = build_payload()["best_combined_routes"]

        self.assertIn("area_gap_exit -> spectral_gap -> Casimir coefficient consistency", routes)
        self.assertIn("spectral_Dirac_levels -> spin_condensate_exit", routes)


if __name__ == "__main__":
    unittest.main()
