import unittest

from scripts.build_p0_eft_janus_z2_sigma_extrinsic_curvature_tensor_builder_gate import build_payload


class P0EFTJanusZ2SigmaExtrinsicCurvatureTensorBuilderGateTests(unittest.TestCase):
    def test_tensor_builder_declares_active_geometry_inputs_only(self):
        payload = build_payload()

        self.assertTrue(payload["extrinsic_curvature_tensor_builder_ready"])
        self.assertTrue(payload["flrw_reduction_ready"])
        self.assertTrue(payload["requires_active_embedding_second_derivatives"])
        self.assertTrue(payload["requires_active_christoffel_symbols"])
        self.assertTrue(payload["requires_active_normal_covector"])
        self.assertTrue(payload["requires_active_spatial_inverse_metric"])
        self.assertFalse(payload["uses_planck_lcdm_inputs"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["K_ab_values_ready"])


if __name__ == "__main__":
    unittest.main()
