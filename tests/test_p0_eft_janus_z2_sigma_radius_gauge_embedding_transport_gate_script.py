import unittest

from scripts.build_p0_eft_janus_z2_sigma_radius_gauge_embedding_transport_gate import build_payload


class P0EFTJanusZ2SigmaRadiusGaugeEmbeddingTransportGateTests(unittest.TestCase):
    def test_radius_gauge_embedding_transport_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["radius_gauge_embedding_transport_ledger_declared"])
        self.assertTrue(payload["declared"]["R_Sigma_of_a_input_declared"])
        self.assertTrue(payload["declared"]["proper_time_gauge_input_declared"])
        self.assertIn("transport", payload["formulas"])

    def test_transport_remains_blocked_until_radius_law_is_ready(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["R_Sigma_of_a_ready"])
        self.assertTrue(payload["closure"]["embedding_gauge_equations_ready"])
        self.assertFalse(payload["closure"]["X_plus_minus_of_a_derived"])
        self.assertFalse(payload["radius_gauge_embedding_transport_ready"])
        self.assertIn("solve_R_Sigma_of_a_from_throat_radius_variational_equation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
