import unittest

from scripts.build_p0_eft_janus_z2_sigma_embedding_tangent_frame_transport_gate import build_payload


class P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGateTests(unittest.TestCase):
    def test_tangent_frame_transport_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_tangent_frame_transport_ledger_declared"])
        self.assertIn("partial X_pm", payload["formulae"]["tangent_frame"])
        self.assertIn("fitted tangent frame", payload["forbidden"])

    def test_tangent_frame_transport_remains_blocked_on_xpm(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["X_plus_minus_of_a_ready"])
        self.assertFalse(payload["closure"]["tangent_frames_from_embedding_ready"])
        self.assertFalse(payload["embedding_tangent_frame_transport_ready"])
        self.assertIn("derive_X_plus_minus_of_a", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
