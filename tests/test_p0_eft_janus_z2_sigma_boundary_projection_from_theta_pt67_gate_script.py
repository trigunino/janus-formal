import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_projection_from_theta_pt67_gate import (
    build_payload,
)


class BoundaryProjectionFromThetaPT67GateTests(unittest.TestCase):
    def test_regular_pt67_theta_projection_gives_zero_unit_charge(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["projection_ready"])
        self.assertTrue(payload["route_B_regular_PT67_exhausted"])
        result = payload["result"]
        self.assertTrue(result["Q_ren_unit_all_zero"])
        self.assertEqual(result["Q_boundary_minus_reference_unit"], [0.0, 0.0, 0.0])
        self.assertFalse(result["can_write_active_z2_sigma_boundary_projection_json"])
        self.assertFalse(result["projected_positive_Friedmann_source_available"])


if __name__ == "__main__":
    unittest.main()
