import unittest

from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_frame_bundle_gate import build_payload


class P0EFTJanusZ2SigmaResolvedTunnelFrameBundleGateTests(unittest.TestCase):
    def test_resolved_tunnel_frame_bundle_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["resolved_tunnel_frame_bundle_ledger_declared"])
        self.assertTrue(payload["declared"]["resolved_tunnel_smooth_atlas_gate_declared"])
        self.assertTrue(payload["declared"]["tangent_bundle_declared"])
        self.assertTrue(payload["declared"]["frame_bundle_declared"])
        self.assertIn("frame_bundle", payload["formulas"])

    def test_resolved_tunnel_frame_bundle_closure_remains_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["projective_tunnel_topology_ready"])
        self.assertFalse(payload["closure"]["resolved_tunnel_atlas_derived"])
        self.assertFalse(payload["closure"]["resolved_tunnel_frame_bundle_ready"])
        self.assertFalse(payload["resolved_tunnel_frame_bundle_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(
            payload["upstream_frontiers"]["resolved_tunnel_smooth_atlas"]["primary_blocker"],
            "R_Sigma_solution_certificate",
        )
        self.assertIn("pass_resolved_tunnel_smooth_atlas_gate", payload["next_required"])
        self.assertIn("feed_result_to_resolved_tunnel_Pin_lift_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
