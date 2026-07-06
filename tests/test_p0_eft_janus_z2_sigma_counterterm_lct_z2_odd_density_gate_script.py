import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_z2_odd_density_gate import (
    build_payload,
)


class CountertermLctZ2OddDensityGateTests(unittest.TestCase):
    def test_lct_oddness_blocks_on_alpha_res_anti_invariance(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["symbolic_primitive_ready"])
        self.assertTrue(payload["closure"]["integration_constant_odd_compatible"])
        self.assertFalse(payload["closure"]["alpha_res_Z2_anti_invariance_proved"])
        self.assertFalse(payload["closure"]["L_ct_Z2_odd_density_proved"])
        self.assertTrue(payload["closure"]["circular_route_detected"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "alpha_res_Z2_anti_invariance")
        self.assertIn("tau_Z2^* L_ct", payload["formulae"]["target"])
        self.assertIn("tau_Z2^* alpha_res", payload["formulae"]["sufficient_condition"])


if __name__ == "__main__":
    unittest.main()
