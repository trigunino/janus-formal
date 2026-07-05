import unittest

from scripts.build_p0_eft_janus_z2_sigma_embedding_regularity_equivariance_gate import build_payload


class P0EFTJanusZ2SigmaEmbeddingRegularityEquivarianceGateTests(unittest.TestCase):
    def test_embedding_regularity_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_regularity_equivariance_ledger_declared"])
        self.assertTrue(payload["declared"]["immersion_rank_test_declared"])
        self.assertTrue(payload["declared"]["Z2_equivariance_test_declared"])
        self.assertIn("rank_test", payload["formulas"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "active_tunnel_embedding_from_RSigma")

    def test_embedding_regularity_remains_blocked_on_xpm(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["X_plus_minus_of_a_derived"])
        self.assertFalse(payload["closure"]["embedding_regularity_equivariance_ready"])
        self.assertFalse(payload["embedding_regularity_equivariance_ready"])
        self.assertIn("pass_active_tunnel_embedding_of_a_gate", payload["next_required"])
        self.assertIn("feed_result_to_sigma_smooth_embedded_throat_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
