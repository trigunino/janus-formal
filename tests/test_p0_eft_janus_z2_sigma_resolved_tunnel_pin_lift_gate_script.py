import unittest

from scripts.build_p0_eft_janus_z2_sigma_resolved_tunnel_pin_lift_gate import build_payload


class P0EFTJanusZ2SigmaResolvedTunnelPinLiftGateTests(unittest.TestCase):
    def test_resolved_tunnel_pin_lift_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["resolved_tunnel_pin_lift_ledger_declared"])
        self.assertTrue(payload["declared"]["resolved_tunnel_frame_bundle_gate_declared"])
        self.assertTrue(payload["declared"]["resolved_tunnel_frame_bundle_declared"])
        self.assertTrue(payload["declared"]["Pin_lift_compatibility_criterion_declared"])
        self.assertIn("pin_lift", payload["formulas"])

    def test_resolved_tunnel_pin_lift_closure_remains_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["Sigma_APS_Pin_lift_ready"])
        self.assertFalse(payload["closure"]["resolved_tunnel_frame_bundle_ready"])
        self.assertFalse(payload["closure"]["resolved_tunnel_Pin_lift_ready"])
        self.assertFalse(payload["resolved_tunnel_pin_lift_ready"])
        self.assertIn("pass_resolved_tunnel_frame_bundle_gate", payload["next_required"])
        self.assertIn("feed_result_to_plus_minus_spinor_bundle_data_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
