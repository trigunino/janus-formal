import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradMetricVariationTransportGateTests(unittest.TestCase):
    def test_delta_h_transport_is_closed_algebraically(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tetrad_metric_variation_transport_ready"])
        self.assertEqual(
            payload["formulae"]["metric_variation"],
            "delta h_ab = eta_IJ(delta e_a^I e_b^J + e_a^I delta e_b^J)",
        )
        self.assertIn("induced_metric_variation_transport_ready", payload["closed"])

    def test_delta_k_and_torsion_remain_open(self):
        payload = build_payload()

        self.assertIn("extrinsic_curvature_variation_transport_ready", payload["still_open"])
        self.assertIn("torsion_pullback_variation_transport_ready", payload["still_open"])
        self.assertTrue(payload["declared"]["no_metric_only_shortcut"])


if __name__ == "__main__":
    unittest.main()
