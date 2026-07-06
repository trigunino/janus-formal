import unittest

from scripts.build_p0_eft_janus_z2_sigma_h0_numeric_input_frontier_gate import (
    build_payload,
)


class H0NumericInputFrontierGateTests(unittest.TestCase):
    def test_scale_free_inputs_exist_but_numeric_h0_inputs_are_not_available(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["numeric_H0_inputs_available"])
        self.assertFalse(payload["can_provide_absolute_RSigma"])
        self.assertFalse(payload["can_provide_state_charge"])
        self.assertFalse(payload["can_provide_action_scale"])
        self.assertTrue(
            payload["nearest_dimensionless_inputs"]["projective_ratio_partial_closure"][
                "exists"
            ]
        )
        self.assertTrue(payload["nearest_dimensionless_inputs"]["scale_free_curvature"]["exists"])


if __name__ == "__main__":
    unittest.main()
