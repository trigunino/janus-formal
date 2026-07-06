import unittest

from scripts.build_p0_eft_janus_z2_sigma_smooth_embedded_throat_gate import build_payload


class P0EFTJanusZ2SigmaSmoothEmbeddedThroatGateTests(unittest.TestCase):
    def test_smooth_embedded_throat_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["sigma_smooth_embedded_throat_ledger_declared"])
        self.assertTrue(payload["declared"]["embedding_regularity_equivariance_gate_declared"])
        self.assertTrue(payload["declared"]["embedded_submanifold_bibliography_checked"])
        self.assertTrue(payload["declared"]["immersion_rank_condition_declared"])
        self.assertIn("rank", payload["formulas"])

    def test_smooth_embedded_throat_remains_blocked_on_active_embedding(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["topological_smooth_embedded_throat_derived"])
        self.assertTrue(payload["topological_smooth_embedded_throat_ready"])
        self.assertFalse(payload["closure"]["active_tunnel_embedding_ready"])
        self.assertFalse(payload["active_metric_smooth_embedded_throat_ready"])
        self.assertTrue(payload["closure"]["sigma_smooth_embedded_throat_derived"])
        self.assertTrue(payload["sigma_smooth_embedded_throat_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertEqual(
            payload["upstream_frontiers"]["active_tunnel_embedding"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("derive_active_metric_embedding_only_if_needed", payload["next_required"])
        self.assertIn("feed_result_to_collar_tubular_neighborhood_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
