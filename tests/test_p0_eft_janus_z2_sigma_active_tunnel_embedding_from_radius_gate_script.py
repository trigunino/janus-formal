import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_from_radius_gate import build_payload


class P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGateTests(unittest.TestCase):
    def test_embedding_from_radius_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["active_embedding_from_radius_ledger_declared"])
        self.assertTrue(payload["declared"]["dynamic_shell_radius_kinematics_imported"])
        self.assertTrue(payload["declared"]["radius_gauge_embedding_transport_gate_declared"])
        self.assertTrue(payload["declared"]["radius_to_embedding_conditional_closure_imported"])
        self.assertTrue(payload["declared"]["R_Sigma_to_X_pm_map_declared"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")

    def test_embedding_remains_blocked_until_radius_law_is_solved(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["R_Sigma_of_a_ready"])
        self.assertTrue(payload["closure"]["embedding_gauge_equations_ready"])
        self.assertFalse(payload["closure"]["X_plus_minus_of_a_ready"])
        self.assertFalse(payload["active_embedding_from_radius_ready"])
        self.assertIn("instantiate_radius_to_embedding_conditional_closure_with_R_Sigma_of_a", payload["next_required"])
        self.assertIn("pass_radius_gauge_embedding_transport_gate", payload["next_required"])
        self.assertIn("solve_R_Sigma_of_a_from_throat_radius_variational_equation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
