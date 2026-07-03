import unittest

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_gate import build_payload


class P0EFTJanusZ2SigmaCoframeConnectionPullbackGateTests(unittest.TestCase):
    def test_coframe_connection_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["coframe_connection_pullback_ledger_declared"])
        self.assertTrue(payload["declared"]["tetrad_coframe_formalism_imported"])
        self.assertTrue(payload["declared"]["spin_connection_formalism_imported"])
        self.assertTrue(payload["declared"]["differential_form_pullback_imported"])
        self.assertTrue(payload["declared"]["tangent_normal_orientation_gate_declared"])
        self.assertTrue(payload["declared"]["projective_gluing_normal_orientation_sign_gate_declared"])

    def test_pullback_remains_blocked_on_active_embedding(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["active_Sigma_embedding_ready"])
        self.assertFalse(payload["closure"]["coframe_pullback_ready"])
        self.assertFalse(payload["closure"]["spin_connection_pullback_ready"])
        self.assertTrue(payload["closure"]["Z2_oriented_pullback_ready"])
        self.assertFalse(payload["coframe_connection_pullback_ready"])
        self.assertIn("pass_active_tunnel_embedding_of_a_gate", payload["next_required"])
        self.assertIn("pass_tangent_normal_orientation_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
