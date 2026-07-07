import unittest

from scripts.build_p0_eft_janus_z2_s4l_projective_scale_geometry_gate import (
    build_payload,
)


class S4LProjectiveScaleGeometryGateTests(unittest.TestCase):
    def test_s4l_geometry_declares_dimensionful_scale(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["topology"]["cover"], "S4_L")
        self.assertTrue(payload["topology"]["global_radius_L_declared"])
        self.assertTrue(payload["topology"]["global_radius_L_dimensionful"])

    def test_current_geometry_does_not_fix_L(self):
        payload = build_payload()

        self.assertFalse(payload["L_fixed_by_current_geometry"])
        self.assertEqual(payload["L_classification"], "continuous_global_state_sector")
        self.assertFalse(payload["no_fit_alpha_ready"])

    def test_all_route_blockers_are_explicit(self):
        payload = build_payload()

        self.assertEqual(set(payload["fixation_routes"]), {
            "global_regularity",
            "boundary_charge",
            "area_or_flux_quantization",
            "holonomy_or_spectral_condition",
        })
        self.assertTrue(all(route["tested"] for route in payload["fixation_routes"].values()))
        self.assertFalse(any(route["fixes_L"] for route in payload["fixation_routes"].values()))


if __name__ == "__main__":
    unittest.main()
