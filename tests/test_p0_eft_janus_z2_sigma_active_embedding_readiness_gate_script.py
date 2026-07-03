import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import build_payload


class P0EFTJanusZ2SigmaActiveEmbeddingReadinessGateTests(unittest.TestCase):
    def test_conditional_embedding_is_ready(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["active_embedding_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["embedding_gauge_equations_ready"])
        self.assertTrue(payload["readiness"]["conditional_radius_to_embedding_ready"])

    def test_active_embedding_waits_for_radius_law(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["R_Sigma_of_a_ready"])
        self.assertFalse(payload["readiness"]["X_plus_minus_of_a_ready"])
        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["active_embedding_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
