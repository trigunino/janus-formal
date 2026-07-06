import unittest

from scripts.build_p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate import build_payload


class P0EFTJanusZ2SigmaCollarTubularNeighborhoodGateTests(unittest.TestCase):
    def test_collar_tubular_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["collar_tubular_neighborhood_ledger_declared"])
        self.assertTrue(payload["declared"]["sigma_smooth_embedded_throat_gate_declared"])
        self.assertTrue(payload["declared"]["collar_neighborhood_bibliography_checked"])
        self.assertTrue(payload["declared"]["tubular_neighborhood_bibliography_checked"])
        self.assertTrue(payload["standard_collar_tubular_theorems_available"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("normal_tube", payload["formulas"])

    def test_collar_tubular_closure_remains_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["sigma_smooth_embedded_derived"])
        self.assertTrue(payload["closure"]["normal_bundle_derived"])
        self.assertTrue(payload["closure"]["collar_tubular_neighborhood_ready"])
        self.assertTrue(payload["collar_tubular_neighborhood_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(
            payload["upstream_frontiers"]["sigma_smooth_embedded_throat"]["active_metric_embedding_ready"]
        )
        self.assertTrue(payload["active_metric_embedding_not_claimed"])
        self.assertIn("keep_active_metric_embedding_separate_from_topological_collar", payload["next_required"])
        self.assertIn("feed_result_to_resolved_tunnel_smooth_atlas_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
