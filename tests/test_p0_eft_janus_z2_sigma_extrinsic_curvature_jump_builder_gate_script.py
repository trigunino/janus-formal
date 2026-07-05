import unittest

from scripts.build_p0_eft_janus_z2_sigma_extrinsic_curvature_jump_builder_gate import build_payload


class P0EFTJanusZ2SigmaExtrinsicCurvatureJumpBuilderGateTests(unittest.TestCase):
    def test_jump_builder_declares_active_inputs_only(self):
        payload = build_payload()

        self.assertTrue(payload["deltaK_jump_builder_ready"])
        self.assertTrue(payload["requires_active_K_s_plus_of_a"])
        self.assertTrue(payload["requires_active_K_s_minus_of_a"])
        self.assertTrue(payload["requires_active_K_tau_plus_of_a"])
        self.assertTrue(payload["requires_active_K_tau_minus_of_a"])
        self.assertTrue(payload["requires_explicit_z2_orientation"])
        self.assertTrue(payload["fitted_orientation_forbidden"])
        self.assertFalse(payload["uses_planck_lcdm_inputs"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["DeltaK_values_ready"])


if __name__ == "__main__":
    unittest.main()
