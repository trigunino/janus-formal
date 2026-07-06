import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_spinor_restriction_gate import build_payload


class P0EFTJanusZ2SigmaBoundarySpinorRestrictionGateTests(unittest.TestCase):
    def test_boundary_spinor_restriction_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["boundary_spinor_restriction_ledger_declared"])
        self.assertTrue(payload["declared"]["plus_boundary_restriction_declared"])
        self.assertTrue(payload["declared"]["minus_boundary_restriction_declared"])
        self.assertTrue(payload["declared"]["Sigma_boundary_spinor_pair_declared"])
        self.assertTrue(payload["declared"]["local_boundary_spinor_variables_declared"])

    def test_local_restriction_is_ready_without_global_bundle_claim(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["active_Sigma_embedding_ready"])
        self.assertFalse(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["global_ambient_spinor_bundle_restriction_ready"])
        self.assertTrue(payload["closure"]["local_boundary_spinor_variables_ready"])
        self.assertTrue(payload["closure"]["Sigma_boundary_spinor_data_ready"])
        self.assertIn("active_embedding", payload["upstream_frontiers"])
        self.assertIn("plus_minus_spinor_bundle_data", payload["upstream_frontiers"])
        self.assertTrue(payload["local_boundary_spinor_restriction_ready"])
        self.assertFalse(payload["global_boundary_spinor_restriction_ready"])
        self.assertTrue(payload["boundary_spinor_restriction_ready"])
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("keep_global_resolved_tunnel_spinor_bundle_unclaimed", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
