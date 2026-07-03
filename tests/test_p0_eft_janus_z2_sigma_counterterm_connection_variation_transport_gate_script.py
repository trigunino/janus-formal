import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_variation_transport_gate import build_payload


class P0EFTJanusZ2SigmaCountertermConnectionVariationTransportGateTests(unittest.TestCase):
    def test_connection_variation_transport_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_connection_variation_transport_ledger_declared"])
        self.assertTrue(payload["declared"]["fixed_embedding_connection_pullback_variation_gate_declared"])
        self.assertIn("delta_omega T^I", payload["formulae"]["fixed_coframe_torsion_variation"])
        self.assertIn("fitted transport coefficient", payload["forbidden"])

    def test_connection_variation_transport_remains_open_until_pullback_is_proved(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["sigma_pullback_ready"])
        self.assertFalse(payload["closure"]["delta_omega_to_delta_torsion_formula_proved"])
        self.assertFalse(payload["counterterm_connection_variation_transport_ready"])
        self.assertIn("pass_fixed_embedding_connection_pullback_variation_gate", payload["next_required"])
        self.assertIn("prove_delta_omega_torsion_formula_on_Sigma", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
