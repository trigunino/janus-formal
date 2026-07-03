import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_one_form_decomposition_gate import build_payload


class P0EFTJanusZ2SigmaCountertermResidualOneFormDecompositionGateTests(unittest.TestCase):
    def test_one_form_channels_are_declared_without_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_residual_one_form_decomposition_ledger_declared"])
        self.assertTrue(payload["declared"]["tetrad_residual_channel_gate_declared"])
        self.assertTrue(payload["declared"]["connection_residual_channel_gate_declared"])
        self.assertTrue(payload["declared"]["spinor_residual_channel_gate_declared"])
        self.assertTrue(payload["declared"]["embedding_residual_channel_gate_declared"])
        self.assertTrue(payload["declared"]["matter_flux_residual_channel_gate_declared"])
        self.assertTrue(payload["declared"]["tetrad_residual_channel_declared"])
        self.assertTrue(payload["declared"]["connection_residual_channel_declared"])
        self.assertTrue(payload["declared"]["spinor_residual_channel_declared"])
        self.assertIn("fit residual coefficient", payload["forbidden"])

    def test_one_form_decomposition_remains_open_until_components_are_explicit(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["residual_one_form_components_explicit"])
        self.assertFalse(payload["counterterm_residual_one_form_decomposition_ready"])
        self.assertIn("compute_tetrad_residual_channel", payload["next_required"])
        self.assertIn("pass_counterterm_tetrad_residual_channel_gate", payload["next_required"])
        self.assertIn("pass_counterterm_connection_residual_channel_gate", payload["next_required"])
        self.assertIn("pass_counterterm_spinor_residual_channel_gate", payload["next_required"])
        self.assertIn("pass_counterterm_embedding_residual_channel_gate", payload["next_required"])
        self.assertIn("pass_counterterm_matter_flux_residual_channel_gate", payload["next_required"])
        self.assertIn("feed_one_form_to_integrability_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
