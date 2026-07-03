import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_tunnel_embedding_of_a_gate import build_payload


class P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGateTests(unittest.TestCase):
    def test_embedding_problem_is_declared_from_bibliography(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["active_tunnel_embedding_problem_declared"])
        self.assertTrue(payload["declared"]["tunnel_embedding_constraint_ledger_declared"])
        self.assertTrue(payload["declared"]["X_plus_of_a_declared"])
        self.assertTrue(payload["declared"]["embedding_from_radius_gate_declared"])
        self.assertIn("arXiv:2412.04644", payload["primary_sources_checked"][0])

    def test_deltaK_of_a_is_blocked_until_xpm_of_a_is_derived(self):
        payload = build_payload()

        self.assertFalse(payload["derived"]["X_plus_minus_of_a_derived"])
        self.assertFalse(payload["derived"]["DeltaK_s_of_a_derived"])
        self.assertFalse(payload["active_tunnel_embedding_of_a_closure_ready"])
        self.assertIn("pass_tunnel_embedding_constraint_count_gate", payload["next_required"])
        self.assertIn("pass_active_tunnel_embedding_from_radius_gate", payload["next_required"])
        self.assertTrue(
            any("derive_X_plus_of_a_and_X_minus_of_a" in item for item in payload["next_required"])
        )


if __name__ == "__main__":
    unittest.main()
