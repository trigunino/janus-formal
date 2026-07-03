import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_normal_tangent_trace_support_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCoupledRadiusFluxNormalTangentTraceSupportGateTests(unittest.TestCase):
    def test_normal_tangent_trace_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["normal_tangent_trace_ledger_declared"])
        self.assertTrue(payload["declared"]["regular_embedding_assumption_declared"])
        self.assertTrue(payload["declared"]["no_independent_frame_fit"])

    def test_support_remains_blocked_until_transported_from_embedding(self):
        payload = build_payload()

        self.assertFalse(payload["support"]["tangent_frame_trace_supported"])
        self.assertFalse(payload["support"]["normal_trace_supported"])
        self.assertFalse(payload["normal_tangent_trace_support_ready"])
        self.assertIn(
            "feed_candidate_indices_support_normal_and_tangent_traces_to_sobolev_index_gate",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
