import unittest

from scripts.build_p0_eft_janus_z2_sigma_embedding_gauge_policy_gate import build_payload


class P0EFTJanusZ2SigmaEmbeddingGaugePolicyGateTests(unittest.TestCase):
    def test_proper_time_gauge_policy_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_gauge_policy_declared"])
        self.assertEqual(payload["gauge_choices"]["shell_time"], "tau = proper time on Sigma")
        self.assertTrue(payload["declared"]["gauge_does_not_fix_throat_radius_declared"])

    def test_gauge_does_not_determine_embedding_without_throat_law(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["gauge_fixing_equations_ready"])
        self.assertFalse(payload["closure"]["gauge_plus_throat_law_determines_Xpm"])
        self.assertFalse(payload["embedding_gauge_closure_ready"])
        self.assertIn("combine_with_throat_radius_law_to_determine_X_plus_minus", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
