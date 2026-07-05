import unittest

from scripts.build_p0_eft_janus_z2_sigma_spinor_bundle_projection_gate import build_payload


class P0EFTJanusZ2SigmaSpinorBundleProjectionGateTests(unittest.TestCase):
    def test_spinor_bundle_projection_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["spinor_bundle_projection_ledger_declared"])
        self.assertTrue(payload["declared"]["spinor_bundle_bibliography_checked"])
        self.assertTrue(payload["declared"]["APS_boundary_spinor_bibliography_checked"])
        self.assertTrue(payload["declared"]["plus_minus_spinor_bundle_data_gate_declared"])
        self.assertTrue(payload["declared"]["boundary_spinor_restriction_gate_declared"])
        self.assertTrue(payload["declared"]["spinor_boundary_projection_map_gate_declared"])
        self.assertTrue(payload["declared"]["Z2Sigma_spinor_projection_declared"])
        self.assertEqual(
            payload["primary_blocker"],
            "plus_minus_spinor_bundle_data",
        )
        self.assertFalse(payload["gate_passed"])

    def test_projection_waits_for_active_spinor_data(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["minus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["Z2Sigma_spinor_projection_ready"])
        self.assertFalse(payload["spinor_bundle_projection_ready"])
        self.assertIn("plus_minus_spinor_bundle_data", payload["upstream_frontiers"])
        self.assertIn("boundary_spinor_restriction", payload["upstream_frontiers"])
        self.assertIn("spinor_boundary_projection_map", payload["upstream_frontiers"])
        self.assertIn("pass_plus_minus_spinor_bundle_data_gate", payload["next_required"])
        self.assertIn("pass_boundary_spinor_restriction_gate", payload["next_required"])
        self.assertIn("pass_spinor_boundary_projection_map_gate", payload["next_required"])
        self.assertIn("derive_Z2Sigma_spinor_projection", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
