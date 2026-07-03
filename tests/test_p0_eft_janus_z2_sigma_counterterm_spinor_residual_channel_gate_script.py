import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_spinor_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermSpinorResidualChannelGateTests(unittest.TestCase):
    def test_spinor_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertTrue(payload["counterterm_spinor_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["projected_spinor_variation_transport_declared"])
        self.assertIn("fit spinor residual coefficient", payload["forbidden"])

    def test_spinor_channel_remains_open_until_coefficients_are_explicit(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["spinor_residual_coefficient_explicit"])
        self.assertFalse(payload["closure"]["conjugate_spinor_residual_coefficient_explicit"])
        self.assertFalse(payload["counterterm_spinor_residual_channel_ready"])


if __name__ == "__main__":
    unittest.main()
