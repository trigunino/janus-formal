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

    def test_restriction_waits_for_embedding_and_spinor_bundles(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["active_Sigma_embedding_ready"])
        self.assertFalse(payload["closure"]["plus_spinor_bundle_ready"])
        self.assertFalse(payload["closure"]["Sigma_boundary_spinor_data_ready"])
        self.assertIn("active_embedding", payload["upstream_frontiers"])
        self.assertIn("plus_minus_spinor_bundle_data", payload["upstream_frontiers"])
        self.assertFalse(payload["boundary_spinor_restriction_ready"])
        self.assertIn("derive_active_Sigma_embedding", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
