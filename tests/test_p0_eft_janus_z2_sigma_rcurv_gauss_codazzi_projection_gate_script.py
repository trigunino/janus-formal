import unittest

from scripts.build_p0_eft_janus_z2_sigma_rcurv_gauss_codazzi_projection_gate import (
    build_payload,
)


class RCurvGaussCodazziProjectionGateTests(unittest.TestCase):
    def test_rcurv_requires_dimensionful_boundary_scale(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["gauss_codazzi_identity_declared"])
        self.assertTrue(payload["closure"]["dimensionless_Rcurv_relation_available"])
        self.assertFalse(payload["closure"]["dimensionful_scale_from_boundary_hamiltonian_available"])
        self.assertFalse(payload["ready_for_background_curvature_input"])
        self.assertIn("do_not_treat_dimensionless_projective_ratio_as_meter_scale", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
