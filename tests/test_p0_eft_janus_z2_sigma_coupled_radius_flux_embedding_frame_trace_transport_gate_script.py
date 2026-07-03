import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_embedding_frame_trace_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCoupledRadiusFluxEmbeddingFrameTraceTransportGateTests(unittest.TestCase):
    def test_conditional_transport_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_frame_trace_transport_ledger_declared"])
        self.assertTrue(payload["declared"]["no_independent_frame_fit"])
        self.assertIn("regular_embedding_ready", payload["conditional_transport_rule"])

    def test_transport_stays_blocked_until_embedding_prerequisites_close(self):
        payload = build_payload()

        self.assertFalse(payload["prerequisites"]["regular_embedding_ready"])
        self.assertFalse(payload["transported"]["candidate_indices_support_normal_and_tangent_traces"])
        self.assertFalse(payload["embedding_frame_trace_transport_ready"])
        self.assertIn("close_embedding_regularity_equivariance_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
