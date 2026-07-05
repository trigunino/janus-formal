import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_trace_regularity_gate import build_payload


class P0EFTJanusZ2SigmaCoupledRadiusFluxTraceRegularityGateTests(unittest.TestCase):
    def test_trace_maps_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["trace_regularity_ledger_declared"])
        self.assertIn("R_Sigma -> n_mu[R_Sigma]|_Sigma", payload["trace_maps"])
        self.assertTrue(payload["declared"]["no_pointwise_product_shortcut"])
        self.assertTrue(payload["analytic_obligations"]["sobolev_trace_threshold_passed"])
        self.assertTrue(payload["analytic_obligations"]["sobolev_product_threshold_passed"])
        self.assertTrue(payload["upstream_frontiers"]["sobolev_threshold_transport"]["ready"])

    def test_trace_regularity_remains_blocked_until_continuity_is_proved(self):
        payload = build_payload()

        self.assertFalse(payload["analytic_obligations"]["embedding_trace_continuous"])
        self.assertFalse(payload["analytic_obligations"]["stress_normal_product_well_defined"])
        self.assertFalse(payload["upstream_frontiers"]["embedding_frame_trace_transport"]["ready"])
        self.assertFalse(payload["trace_regularity_ready"])
        self.assertIn("flux_functional_trace_ready = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
