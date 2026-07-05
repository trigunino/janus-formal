import unittest

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_component_builder_gate import build_payload


class P0EFTJanusZ2SigmaCartanGHYComponentBuilderGateTests(unittest.TestCase):
    def test_builder_gate_declares_strict_delta_k_requirements(self):
        payload = build_payload()

        self.assertTrue(payload["deltaK_to_component_builder_ready"])
        self.assertTrue(payload["requires_active_DeltaK_s_of_a"])
        self.assertTrue(payload["requires_active_DeltaK_tau_of_a"])
        self.assertTrue(payload["requires_explicit_kappa_rho_crit0"])
        self.assertFalse(payload["uses_planck_lcdm_normalization"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["cartan_ghy_component_values_ready"])


if __name__ == "__main__":
    unittest.main()
