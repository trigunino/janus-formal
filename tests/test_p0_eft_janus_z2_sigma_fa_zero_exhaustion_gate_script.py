import unittest

from scripts.build_p0_eft_janus_z2_sigma_fa_zero_exhaustion_gate import build_payload


class P0EFTJanusZ2SigmaFaZeroExhaustionGateTests(unittest.TestCase):
    def test_fa_zero_route_is_promising_not_promoted(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["promising_not_rustine"])
        self.assertFalse(payload["active_sigma_transparency_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertEqual(payload["best_current_subroute"], "perfect_fluid_plus_torsionless_Holst_boundary_flux")

    def test_exhaustion_records_all_live_routes(self):
        payload = build_payload()
        routes = payload["routes"]

        self.assertIn("perfect_fluid_tangential", routes)
        self.assertIn("flow_tangency", routes)
        self.assertIn("holst_torsion_flux", routes)
        self.assertIn("z2_equivariant_total_stress", routes)
        self.assertIn("stress_transport", routes)
        self.assertIn("no_normal_dirac_current", routes)
        self.assertEqual(routes["perfect_fluid_tangential"]["status"], "partial_matter_route")
        self.assertEqual(routes["flow_tangency"]["status"], "computed_u_dot_n_and_e_dot_n_route")
        self.assertEqual(routes["holst_torsion_flux"]["status"], "local_Sigma_Holst_flux_route")
        self.assertEqual(routes["z2_equivariant_total_stress"]["status"], "total_flux_route")

    def test_next_required_targets_physics_not_fit(self):
        payload = build_payload()

        self.assertNotIn("Holst_torsion_flux_zero_or_Z2_equivariance", payload["hard_remaining_blockers"])
        self.assertIn("normal_dirac_current_zero_via_reflecting_or_Z2_parity", payload["hard_remaining_blockers"])
        self.assertIn("spinor_equivariance_routes_open", payload["hard_remaining_blockers"])
        self.assertIn("spinor_soldering_boundary_variation_residual", payload["hard_remaining_blockers"])
        self.assertIn("resolved_tunnel_Pin_lift_for_spinor_descent", payload["hard_remaining_blockers"])
        self.assertNotIn("close_perfect_fluid_matter_flux_zero", payload["next_required"])
        self.assertNotIn("handle_Holst_torsion_flux_by_Z2_equivariance_or_zero_projection", payload["next_required"])
        self.assertIn(
            "close_normal_dirac_current_by_reflecting_boundary_or_Z2_current_parity",
            payload["next_required"],
        )
        self.assertIn("close_spinor_soldering_boundary_variation_residual", payload["next_required"])
        self.assertIn("or_close_spinor_quotient_descent_equivariance", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
