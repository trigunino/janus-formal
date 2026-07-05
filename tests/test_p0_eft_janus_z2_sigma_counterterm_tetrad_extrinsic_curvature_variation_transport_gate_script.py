import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradExtrinsicCurvatureVariationTransportGateTests(unittest.TestCase):
    def test_deltaK_variation_channels_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["deltaK_transport_ledger_declared"])
        self.assertIn("delta e_a", payload["formulae"]["variation_channels"])
        self.assertIn("delta K_ab", payload["formulae"]["structural_variation"])
        self.assertTrue(payload["closure"]["delta_K_structural_formula_ready"])
        self.assertTrue(payload["partial_subchannels"]["structural_variation_formula"]["ready"])
        self.assertTrue(payload["declared"]["no_fitted_extrinsic_curvature_variation"])

    def test_deltaK_transport_remains_blocked_on_embedding_and_connection(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["active_embedding_ready"])
        self.assertTrue(payload["closure"]["delta_K_structural_formula_ready"])
        self.assertFalse(payload["closure"]["connection_variation_transport_ready"])
        self.assertFalse(payload["upstream_frontiers"]["active_embedding"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["frame_trace_transport"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["connection_variation"]["ready"])
        self.assertFalse(payload["closure"]["delta_K_upstream_transport_inputs_ready"])
        self.assertFalse(payload["closure"]["delta_K_in_allowed_basis"])
        self.assertFalse(payload["deltaK_transport_ready"])
        self.assertIn("close_active_tunnel_embedding_of_a_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
