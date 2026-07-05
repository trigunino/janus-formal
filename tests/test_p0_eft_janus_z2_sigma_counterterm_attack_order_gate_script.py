import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_attack_order_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermAttackOrderGateTests(unittest.TestCase):
    def test_attack_order_detects_radius_counterterm_cycle(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["attack_order_is_diagnostic_only"])
        self.assertTrue(payload["declared"]["no_legacy_z4_import"])
        self.assertTrue(payload["declared"]["circular_radius_counterterm_dependency_checked"])
        self.assertTrue(payload["declared"]["symbolic_local_counterterm_route_declared"])
        self.assertEqual(payload["primary_blocker"], "counterterm_coefficient_expansion")
        self.assertTrue(payload["closure"]["radius_counterterm_circular_dependency_detected"])
        self.assertFalse(payload["closure"]["R_Sigma_solution_certificate_ready"])
        self.assertFalse(payload["closure"]["active_embedding_ready"])
        self.assertTrue(payload["closure"]["symbolic_local_counterterm_route_ready"])
        self.assertFalse(payload["closure"]["counterterm_coefficient_expansion_explicit"])
        self.assertFalse(payload["gate_passed"])

    def test_tetrad_is_nearest_channel_but_not_ready(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["nearest_channel_identified"])
        self.assertTrue(payload["closure"]["tetrad_channel_is_nearest_not_ready"])
        self.assertIn(
            "derive_counterterm_residual_symbolically_in_local_boundary_basis",
            payload["attack_order"],
        )
        self.assertIn(
            "derive_counterterm_residual_scalar_contractions_inputs",
            payload["attack_order"],
        )
        self.assertIn(
            "expand_residual_coefficients_R_h_R_K_R_T_R_chi_in_allowed_basis",
            payload["next_required"],
        )
        self.assertIn(
            "run_counterterm_lct_radial_profile_from_residual_contractions",
            payload["next_required"],
        )
        self.assertTrue(payload["upstream_frontiers"]["symbolic_local_primitive"]["ready"])
        self.assertFalse(
            payload["upstream_frontiers"]["residual_channel_frontier"]["ready"]
        )


if __name__ == "__main__":
    unittest.main()
