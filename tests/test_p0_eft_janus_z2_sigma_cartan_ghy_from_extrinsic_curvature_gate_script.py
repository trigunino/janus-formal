import unittest

from scripts.build_p0_eft_janus_z2_sigma_cartan_ghy_from_extrinsic_curvature_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCartanGHYFromExtrinsicCurvatureGateTests(unittest.TestCase):
    def test_gate_declares_strict_composition_requirements(self):
        payload = build_payload()

        self.assertTrue(payload["cartan_ghy_from_K_plus_minus_builder_ready"])
        self.assertTrue(payload["composes_DeltaK_jump_builder"])
        self.assertTrue(payload["composes_Cartan_GHY_component_builder"])
        self.assertTrue(payload["requires_active_K_plus_minus_of_a"])
        self.assertTrue(payload["requires_explicit_z2_orientation"])
        self.assertTrue(payload["requires_explicit_kappa_rho_crit0"])
        self.assertFalse(payload["uses_planck_lcdm_inputs"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["cartan_ghy_values_ready"])


if __name__ == "__main__":
    unittest.main()
