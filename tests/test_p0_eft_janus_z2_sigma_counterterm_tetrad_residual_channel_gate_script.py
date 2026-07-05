import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermTetradResidualChannelGateTests(unittest.TestCase):
    def test_tetrad_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_tetrad_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["coframe_variation_basis_declared"])
        self.assertIn("fit tetrad residual coefficient", payload["forbidden"])
        self.assertIn("delta h_ab from delta e", payload["transport_targets"])

    def test_tetrad_channel_remains_open_until_coefficient_is_explicit(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["tetrad_metric_residual_subchannel_explicit"])
        self.assertTrue(
            payload["closure"]["tetrad_metric_residual_coefficient_formula_declared"]
        )
        self.assertFalse(
            payload["closure"]["tetrad_metric_residual_coefficient_value_ready"]
        )
        self.assertIn("metric_residual_coefficient_writer", payload["upstream_frontiers"])
        self.assertFalse(payload["upstream_frontiers"]["metric_residual_coefficient_writer"]["ready"])
        self.assertTrue(payload["partial_subchannels"]["metric"]["ready"])
        self.assertIn("R_e_metric", payload["partial_subchannels"]["metric"]["residual_coefficient"])
        self.assertFalse(payload["closure"]["tetrad_residual_coefficient_explicit"])
        self.assertFalse(payload["closure"]["tetrad_variation_transport_ready"])
        self.assertFalse(
            payload["closure"]["active_sigma_boundary_variation_residual_formula_ready"]
        )
        self.assertFalse(payload["upstream_frontiers"]["tetrad_variation_transport"]["ready"])
        self.assertFalse(payload["counterterm_tetrad_residual_channel_ready"])
        self.assertIn("compute_R_e_from_active_sigma_boundary_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
