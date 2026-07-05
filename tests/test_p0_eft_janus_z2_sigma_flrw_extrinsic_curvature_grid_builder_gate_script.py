import unittest

from scripts.build_p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_grid_builder_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridBuilderGateTests(unittest.TestCase):
    def test_grid_builder_declares_active_geometry_inputs_only(self):
        payload = build_payload()

        self.assertTrue(payload["flrw_K_grid_builder_ready"])
        self.assertTrue(payload["composes_metric_geometry_primitives"])
        self.assertTrue(payload["composes_extrinsic_curvature_tensor_builder"])
        self.assertTrue(payload["produces_K_s_of_a_array"])
        self.assertTrue(payload["produces_K_tau_of_a_array"])
        self.assertTrue(payload["requires_active_a_grid"])
        self.assertTrue(payload["requires_active_tangent_vectors"])
        self.assertTrue(payload["requires_active_second_embedding"])
        self.assertTrue(payload["requires_active_christoffel_symbols"])
        self.assertTrue(payload["requires_active_normal_covector"])
        self.assertTrue(payload["requires_active_spatial_inverse_metric"])
        self.assertFalse(payload["uses_planck_lcdm_inputs"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["K_s_tau_values_ready"])


if __name__ == "__main__":
    unittest.main()
