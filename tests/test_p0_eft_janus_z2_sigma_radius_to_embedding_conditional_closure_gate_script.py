import unittest

from scripts.build_p0_eft_janus_z2_sigma_radius_to_embedding_conditional_closure_gate import build_payload


class P0EFTJanusZ2SigmaRadiusToEmbeddingConditionalClosureGateTests(unittest.TestCase):
    def test_conditional_embedding_map_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["conditional_embedding_ledger_declared"])
        self.assertTrue(payload["radius_to_embedding_conditional_ready"])
        self.assertTrue(payload["conditional"]["X_plus_minus_conditionally_derived"])
        self.assertIn("conditional_transport", payload["formulas"])

    def test_unconditional_embedding_remains_blocked_on_radius_law(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["R_Sigma_of_a_ready"])
        self.assertFalse(payload["closure"]["X_plus_minus_of_a_ready"])
        self.assertFalse(payload["radius_to_embedding_unconditional_ready"])
        self.assertIn("solve_R_Sigma_of_a_from_throat_radius_variational_equation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
