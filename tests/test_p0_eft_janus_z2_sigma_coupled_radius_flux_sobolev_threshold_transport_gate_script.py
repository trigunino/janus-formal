import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_sobolev_threshold_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCoupledRadiusFluxSobolevThresholdTransportGateTests(unittest.TestCase):
    def test_trace_and_product_thresholds_are_transported(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["threshold_transport_ledger_declared"])
        self.assertTrue(payload["trace_and_product_thresholds_transported"])
        self.assertIn("candidate_indices_pass_trace_threshold", payload["closed_from_sobolev_theorems"])
        self.assertIn("candidate_indices_pass_product_threshold", payload["closed_from_sobolev_theorems"])

    def test_normal_tangent_support_remains_open(self):
        payload = build_payload()

        self.assertTrue(payload["transported"]["normal_and_tangent_frame_support_still_open"])
        self.assertIn("candidate_indices_support_normal_and_tangent_traces", payload["still_open"])
        self.assertIn(
            "prove_normal_trace_continuity_for_RSigma_regular_embeddings",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
