import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_frontier_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxFrontierGateTests(unittest.TestCase):
    def test_frontier_ledger_and_routes_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_frontier_ledger_declared"])
        self.assertIn("transparency", payload["routes"])
        self.assertIn("active_projection", payload["routes"])

    def test_frontier_reduces_radial_block_through_perfect_fluid_route(self):
        payload = build_payload()

        self.assertFalse(payload["matter_flux_transparency_path_ready"])
        self.assertFalse(payload["matter_flux_active_projection_path_ready"])
        self.assertTrue(payload["matter_flux_frontier_ready"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("active_flux_projection_ready = false", payload["current_frontier"])
        self.assertTrue(payload["paths"]["route_decision_ready"])
        self.assertTrue(payload["paths"]["matter_flux_radial_block_reduced"])
        self.assertTrue(payload["paths"]["perfect_fluid_tangential_radial_zero_ready"])
        self.assertFalse(
            payload["upstream_frontiers"]["perfect_fluid_tangential_zero"][
                "active_sigma_transparency_claimed"
            ]
        )
        self.assertFalse(payload["upstream_frontiers"]["transparency"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["active_projection"]["ready"])
        self.assertTrue(payload["upstream_frontiers"]["acyclicity"]["ready"])
        self.assertIn("then_reduce_E_matterFlux_radial_block", payload["next_required"])
        self.assertTrue(payload["nearest_matter_flux_route_frontier_declared"])
        self.assertTrue(payload["nearest_matter_flux_route_frontier_diagnostic_only"])
        self.assertEqual(payload["nearest_matter_flux_route_frontier"]["route"], "transparency")
        self.assertEqual(
            payload["nearest_matter_flux_route_frontier"]["gate"],
            "P0EFTJanusZ2SigmaMatterFluxTransparencyGate",
        )
        self.assertIn(
            "derive J_n^Z2Sigma = 0 from active projected currents",
            payload["nearest_matter_flux_route_frontier"]["required"],
        )


if __name__ == "__main__":
    unittest.main()
