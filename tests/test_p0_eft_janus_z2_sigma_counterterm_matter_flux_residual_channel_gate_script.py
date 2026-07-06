import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_matter_flux_residual_channel_gate import build_payload


class P0EFTJanusZ2SigmaCountertermMatterFluxResidualChannelGateTests(unittest.TestCase):
    def test_matter_flux_channel_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertTrue(payload["counterterm_matter_flux_residual_channel_ledger_declared"])
        self.assertTrue(payload["declared"]["normal_tangent_flux_formula_declared"])
        self.assertIn("fit matter residual coefficient", payload["forbidden"])

    def test_matter_flux_channel_closes_for_selected_perfect_fluid_tangential_branch(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["matter_residual_coefficient_explicit"])
        self.assertTrue(payload["closure"]["matter_flux_frontier_ready"])
        self.assertTrue(payload["closure"]["matter_residual_formula_from_flux_variation_ready"])
        self.assertTrue(payload["upstream_frontiers"]["matter_flux"]["ready"])
        self.assertTrue(payload["counterterm_matter_flux_residual_channel_ready"])
        self.assertEqual(payload["residual_coefficient"]["value"], "0")
        self.assertEqual(
            payload["residual_coefficient"]["scope"],
            "perfect_fluid_tangential_matter_sector",
        )
        self.assertFalse(payload["residual_coefficient"]["full_sigma_transparency_claimed"])


if __name__ == "__main__":
    unittest.main()
