import unittest

from scripts.build_p0_eft_janus_z2_sigma_fixed_embedding_connection_pullback_variation_gate import build_payload


class P0EFTJanusZ2SigmaFixedEmbeddingConnectionPullbackVariationGateTests(unittest.TestCase):
    def test_fixed_embedding_pullback_variation_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["fixed_embedding_connection_pullback_variation_ledger_declared"])
        self.assertTrue(payload["declared"]["connection_only_fixed_embedding_variation_gate_declared"])
        self.assertTrue(payload["declared"]["fixed_map_pullback_variation_commutation_gate_declared"])
        self.assertTrue(payload["declared"]["oriented_pullback_variation_commutation_gate_declared"])
        self.assertIn("delta_omega X_Sigma", payload["formulae"]["hidden_embedding_excluded"])
        self.assertIn("hide delta X inside delta omega", payload["forbidden"])

    def test_fixed_embedding_pullback_variation_remains_open(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["fixed_embedding_condition_proved"])
        self.assertTrue(payload["closure"]["pullback_commutes_with_delta_omega"])
        self.assertTrue(payload["closure"]["z2_oriented_commutation_ready"])
        self.assertFalse(payload["fixed_embedding_connection_pullback_variation_ready"])
        self.assertIn("pass_active_tunnel_embedding_of_a_gate", payload["next_required"])
        self.assertIn("pass_coframe_connection_pullback_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
