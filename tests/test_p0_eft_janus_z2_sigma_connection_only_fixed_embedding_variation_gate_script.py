import unittest

from scripts.build_p0_eft_janus_z2_sigma_connection_only_fixed_embedding_variation_gate import build_payload


class P0EFTJanusZ2SigmaConnectionOnlyFixedEmbeddingVariationGateTests(unittest.TestCase):
    def test_connection_only_fixed_embedding_variation_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["connection_only_fixed_embedding_variation_ledger_declared"])
        self.assertTrue(payload["closure"]["delta_omega_XSigma_zero_proved"])
        self.assertTrue(payload["connection_only_fixed_embedding_variation_ready"])

    def test_connection_only_variation_keeps_channels_separated(self):
        payload = build_payload()

        self.assertIn("delta_omega X_Sigma = 0", payload["formulae"]["connection_only_condition"])
        self.assertIn("hide delta X inside delta omega", payload["forbidden"])
        self.assertIn("collapse R_omega and R_X channels", payload["forbidden"])
        self.assertIn(
            "feed_delta_omega_XSigma_zero_to_fixed_embedding_pullback_variation_gate",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
