import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradVariationTransportGateTests(unittest.TestCase):
    def test_tetrad_variation_transport_targets_are_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tetrad_variation_transport_ledger_declared"])
        self.assertIn("delta e -> delta h_ab", payload["transport_targets"])
        self.assertTrue(payload["declared"]["no_metric_only_shortcut"])

    def test_transport_remains_blocked_until_all_targets_are_derived(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["induced_metric_variation_transport_ready"])
        self.assertFalse(payload["closure"]["extrinsic_curvature_variation_transport_ready"])
        self.assertFalse(payload["closure"]["torsion_pullback_variation_transport_ready"])
        self.assertFalse(payload["closure"]["tetrad_variation_transport_ready"])
        self.assertIn("metric_variation", payload["upstream_frontiers"])
        self.assertIn(
            "feed_tetrad_variation_transport_to_tetrad_residual_channel_gate",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
