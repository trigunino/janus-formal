import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_connection_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermConnectionResidualChannelGateTests(unittest.TestCase):
    def test_connection_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_connection_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["connection_variation_transport_gate_declared"])
        self.assertTrue(payload["declared"]["spin_connection_variation_basis_declared"])
        self.assertIn("connection_variation_transport", payload["upstream_frontiers"])
        self.assertTrue(
            payload["closure"]["fixed_embedding_commutation_subchannel_ready"]
        )
        self.assertTrue(
            payload["partial_subchannels"][
                "fixed_embedding_commutation_to_connection_channel"
            ]["ready"]
        )
        self.assertIn("fit connection residual coefficient", payload["forbidden"])
        self.assertIn("delta torsion pullback from delta omega", payload["transport_targets"])

    def test_connection_channel_closes_via_torsionless_fixed_embedding_coefficient(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["connection_variation_transport_ready"])
        self.assertTrue(payload["closure"]["torsion_pullback_coefficient_zero"])
        self.assertTrue(payload["closure"]["connection_residual_coefficient_explicit"])
        self.assertTrue(payload["counterterm_connection_residual_channel_ready"])
        self.assertEqual(payload["residual_coefficient"]["R_omega"], "0")
        self.assertEqual(
            payload["residual_coefficient"]["scope"],
            "connection_only_fixed_embedding_torsionless_sigma_branch",
        )
        self.assertFalse(payload["residual_coefficient"]["full_connection_transport_claimed"])


if __name__ == "__main__":
    unittest.main()
