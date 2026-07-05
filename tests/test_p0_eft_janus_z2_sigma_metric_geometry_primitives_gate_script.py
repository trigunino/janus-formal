import unittest

from scripts.build_p0_eft_janus_z2_sigma_metric_geometry_primitives_gate import build_payload


class P0EFTJanusZ2SigmaMetricGeometryPrimitivesGateTests(unittest.TestCase):
    def test_metric_geometry_gate_declares_active_inputs_only(self):
        payload = build_payload()

        self.assertTrue(payload["metric_inverse_builder_ready"])
        self.assertTrue(payload["christoffel_builder_ready"])
        self.assertTrue(payload["unit_normal_from_level_set_ready"])
        self.assertTrue(payload["induced_metric_pullback_ready"])
        self.assertTrue(payload["requires_active_metric"])
        self.assertTrue(payload["requires_active_metric_derivatives"])
        self.assertTrue(payload["requires_explicit_normal_norm_sign"])
        self.assertTrue(payload["requires_explicit_orientation_sign"])
        self.assertFalse(payload["uses_planck_lcdm_inputs"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["metric_geometry_values_ready"])


if __name__ == "__main__":
    unittest.main()
