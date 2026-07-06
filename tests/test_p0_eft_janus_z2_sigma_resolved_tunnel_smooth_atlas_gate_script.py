import unittest

from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_smooth_atlas_gate import build_payload


class P0EFTJanusZ2SigmaResolvedTunnelSmoothAtlasGateTests(unittest.TestCase):
    def test_resolved_tunnel_smooth_atlas_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["resolved_tunnel_smooth_atlas_ledger_declared"])
        self.assertTrue(payload["declared"]["collar_tubular_neighborhood_gate_declared"])
        self.assertTrue(payload["declared"]["tubular_neighborhood_bibliography_checked"])
        self.assertTrue(payload["declared"]["collar_gluing_bibliography_checked"])
        self.assertTrue(payload["standard_smooth_gluing_theorems_available"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("atlas", payload["formulas"])

    def test_resolved_tunnel_smooth_atlas_closure_remains_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["projective_tunnel_topology_ready"])
        self.assertTrue(payload["closure"]["resolved_tunnel_atlas_derived"])
        self.assertTrue(payload["closure"]["smooth_atlas_ready"])
        self.assertTrue(payload["resolved_tunnel_smooth_atlas_ready"])
        self.assertTrue(payload["gate_passed"])
        self.assertFalse(
            payload["upstream_frontiers"]["collar_tubular_neighborhood"]["active_metric_embedding_ready"]
        )
        self.assertTrue(payload["active_metric_embedding_not_claimed"])
        self.assertIn("keep_active_metric_embedding_separate_from_topological_atlas", payload["next_required"])
        self.assertIn("feed_result_to_resolved_tunnel_frame_bundle_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
