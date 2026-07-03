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

        self.assertFalse(payload["closure"]["tetrad_residual_coefficient_explicit"])
        self.assertFalse(payload["counterterm_tetrad_residual_channel_ready"])
        self.assertIn("compute_R_e_from_active_sigma_boundary_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
