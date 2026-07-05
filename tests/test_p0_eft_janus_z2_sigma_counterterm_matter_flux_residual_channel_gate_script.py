import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGateTests(unittest.TestCase):
    def test_matter_flux_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertTrue(payload["counterterm_matter_flux_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["normal_tangent_flux_formula_declared"])
        self.assertIn("fit matter residual coefficient", payload["forbidden"])

    def test_matter_flux_channel_remains_open_until_coefficient_is_explicit(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["matter_residual_coefficient_explicit"])
        self.assertFalse(payload["closure"]["matter_flux_frontier_ready"])
        self.assertFalse(payload["closure"]["matter_residual_formula_from_flux_variation_ready"])
        self.assertFalse(payload["upstream_frontiers"]["matter_flux"]["ready"])
        self.assertFalse(payload["counterterm_matter_flux_residual_channel_ready"])
        self.assertIn("compute_R_matter_from_active_normal_flux_variation", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
