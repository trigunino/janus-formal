import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_variation_transport_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermTetradVariationTransportReadinessGateTests(unittest.TestCase):
    def test_readiness_aggregates_subgate_status(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["tetrad_variation_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["induced_metric_variation_transport_ready"])
        self.assertTrue(payload["upstream_frontiers"]["metric_variation"]["ready"])
        self.assertEqual(
            payload["subgate_status"]["delta_e_to_delta_h"],
            "closed_by_tetrad_metric_variation_transport_gate",
        )
        self.assertEqual(payload["nearest_missing_subgate"]["name"], "delta_e_to_delta_K")
        self.assertEqual(
            payload["nearest_missing_subgate"]["gate"],
            "counterterm_tetrad_extrinsic_curvature_variation_transport_gate",
        )

    def test_parent_transport_remains_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["extrinsic_curvature_variation_transport_ready"])
        self.assertFalse(payload["readiness"]["torsion_pullback_variation_transport_ready"])
        self.assertFalse(payload["upstream_frontiers"]["extrinsic_curvature_variation"]["ready"])
        self.assertFalse(payload["upstream_frontiers"]["torsion_pullback_variation"]["ready"])
        self.assertFalse(payload["tetrad_variation_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
