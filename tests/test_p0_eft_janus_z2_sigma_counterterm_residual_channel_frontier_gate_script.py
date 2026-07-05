import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_channel_frontier_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermResidualChannelFrontierGateTests(unittest.TestCase):
    def test_channel_frontier_declares_all_residual_coefficients(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["residual_channel_frontier_ledger_declared"])
        self.assertIn("R_e tetrad/coframe coefficient", payload["channel_coefficients"])
        self.assertIn("R_matter matter-flux coefficient", payload["channel_coefficients"])

    def test_frontier_remains_blocked_until_all_channels_close(self):
        payload = build_payload()

        self.assertFalse(payload["channels"]["tetrad_residual_ready"])
        self.assertFalse(payload["channels"]["all_residual_channels_explicit"])
        self.assertFalse(payload["channel_frontiers"]["tetrad"]["ready"])
        self.assertFalse(payload["channel_frontiers"]["matter_flux"]["ready"])
        self.assertEqual(payload["nearest_residual_channel_frontier"]["channel"], "tetrad")
        self.assertTrue(
            payload["nearest_residual_channel_frontier"]["transport_closed_coefficients_open"]
        )
        self.assertIn(
            "tetrad_residual_coefficient_explicit",
            payload["nearest_residual_channel_frontier"]["remaining_false_closure_fields"],
        )
        self.assertEqual(payload["primary_blocker"], "tetrad_residual_coefficients")
        self.assertFalse(payload["residual_channel_frontier_ready"])
        self.assertIn(
            "derive_tetrad_residual_coefficients_R_h_R_K_R_T_R_chi",
            payload["next_required"],
        )
        self.assertIn("feed_all_coefficients_to_residual_one_form_decomposition_gate", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
