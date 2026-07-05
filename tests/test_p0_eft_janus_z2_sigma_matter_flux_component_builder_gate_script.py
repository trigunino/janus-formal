import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_component_builder_gate import build_payload


class P0EFTJanusZ2SigmaMatterFluxComponentBuilderGateTests(unittest.TestCase):
    def test_matter_flux_builder_declares_transparency_guard(self):
        payload = build_payload()

        self.assertTrue(payload["transparent_flux_component_builder_ready"])
        self.assertTrue(payload["requires_active_sigma_transparency_derived"])
        self.assertTrue(payload["matter_flux_zero_without_transparency_forbidden"])
        self.assertFalse(payload["matter_flux_rho_p_values_ready"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_archived_z4_inputs"])


if __name__ == "__main__":
    unittest.main()
