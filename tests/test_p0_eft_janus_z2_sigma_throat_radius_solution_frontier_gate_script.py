import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import build_payload


class P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGateTests(unittest.TestCase):
    def test_frontier_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_solution_frontier_ledger_declared"])
        self.assertTrue(payload["status_flags"]["variational_equation_ready"])
        self.assertTrue(payload["status_flags"]["conditional_embedding_map_ready"])
        self.assertIn("variational_equation", payload["upstream_frontiers"])
        self.assertIn("radius_to_embedding", payload["upstream_frontiers"])
        self.assertFalse(
            payload["upstream_frontiers"]["variational_equation"]["closure_ready"]
        )
        self.assertFalse(
            payload["upstream_frontiers"]["radius_to_embedding"]["unconditional_ready"]
        )

    def test_solution_certificate_now_blocks_on_counterterm_coefficients(self):
        payload = build_payload()

        self.assertTrue(payload["status_flags"]["matter_flux_block_reduced"])
        self.assertTrue(
            payload["status_flags"]["matter_flux_transparency_or_projection_frontier_ready"]
        )
        self.assertFalse(payload["status_flags"]["coupled_radius_flux_solution_ready"])
        self.assertFalse(payload["status_flags"]["counterterm_block_reduced"])
        self.assertTrue(payload["upstream_frontiers"]["matter_flux_frontier"]["frontier_ready"])
        self.assertFalse(payload["upstream_frontiers"]["coupled_radius_flux"]["solution_ready"])
        self.assertFalse(payload["upstream_frontiers"]["counterterm"]["reduction_ready"])
        self.assertFalse(payload["throat_radius_solution_certificate_ready"])
        self.assertFalse(payload["embedding_unblocked_by_radius_solution"])
        self.assertEqual(payload["primary_blocker"], "counterterm_radial_block")
        self.assertEqual(payload["nearest_primary_blocker"], "counterterm_coefficient_expansion")
        self.assertEqual(
            payload["upstream_frontiers"]["matter_flux_frontier"]["primary_blocker"],
            "none",
        )
        self.assertIn(
            "counterterm_block_reduced = false via CountertermRadialReductionFrontierGate",
            payload["current_frontier"],
        )
        self.assertIn("cartan_ghy", payload["nearest_radial_block_frontier"])
        self.assertIn("matter_flux", payload["nearest_radial_block_frontier"])
        self.assertIn(
            "frontier_route",
            payload["nearest_radial_block_frontier"]["matter_flux"],
        )
        self.assertIn(
            "coupled_route",
            payload["nearest_radial_block_frontier"]["matter_flux"],
        )
        self.assertIn("counterterm", payload["nearest_radial_block_frontier"])
        self.assertIn(
            "do not fit R_Sigma(a)",
            payload["nearest_radial_block_frontier"]["priority_rule"],
        )
        self.assertTrue(payload["nearest_unresolved_radial_block_declared"])
        self.assertTrue(payload["nearest_unresolved_radial_block_diagnostic_only"])
        self.assertEqual(payload["nearest_unresolved_radial_block"]["block"], "counterterm")
        self.assertEqual(
            payload["nearest_unresolved_radial_block"]["primary_blocker"],
            "counterterm_coefficient_expansion",
        )
        self.assertEqual(
            payload["nearest_unresolved_radial_block"]["gate"],
            "P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGate",
        )
        self.assertIn(
            "extract residual one-form coefficients",
            payload["nearest_unresolved_radial_block"]["required"],
        )


if __name__ == "__main__":
    unittest.main()
