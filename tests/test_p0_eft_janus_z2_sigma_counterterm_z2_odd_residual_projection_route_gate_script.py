import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_z2_odd_residual_projection_route_gate import (
    build_payload,
)


class CountertermZ2OddResidualProjectionRouteGateTests(unittest.TestCase):
    def test_z2_odd_bypass_is_declared_but_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["Z2_orientation_reversal_available"])
        self.assertTrue(payload["declared"]["counterterm_density_bypass_requires_anti_invariance"])
        self.assertTrue(payload["closure"]["paired_sheet_residual_support_proved"])
        self.assertTrue(payload["paired_sheet_support_route"]["ready"])
        self.assertIn("two-fold tunnel cover", payload["paired_sheet_support_route"]["basis"])
        self.assertFalse(payload["closure"]["alpha_res_Z2_anti_invariance_proved"])
        self.assertFalse(payload["closure"]["E_counterterm_zero_without_density"])
        self.assertFalse(payload["route_ready"])
        self.assertEqual(payload["primary_blocker"], "alpha_res_Z2_anti_invariance")
        self.assertIn("tau_Z2^* alpha_res", payload["route_formula"]["anti_invariance"])


if __name__ == "__main__":
    unittest.main()
