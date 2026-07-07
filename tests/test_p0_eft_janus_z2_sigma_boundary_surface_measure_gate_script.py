import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_surface_measure_gate import (
    build_payload,
)


class BoundarySurfaceMeasureGateTests(unittest.TestCase):
    def test_symbolic_surface_measure_is_ready_but_absolute_radius_is_not(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["symbolic_surface_measure_ready"])
        self.assertFalse(payload["numeric_surface_measure_ready"])
        self.assertFalse(payload["natural_scale_gate"]["accepted_as_RSigma"])
        self.assertIn("R_Sigma^3", payload["surface_measure_formula"])
        self.assertIn("absolute_RSigma_available", payload["blocked_by"])


if __name__ == "__main__":
    unittest.main()
