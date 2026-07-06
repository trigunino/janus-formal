import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_component_parity_gate import (
    build_payload,
)


class CountertermTetradComponentParityGateTests(unittest.TestCase):
    def test_variation_parities_ready_but_coefficient_parities_block(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["metric_variation_parity_ready"])
        self.assertTrue(payload["closure"]["extrinsic_variation_parity_ready"])
        self.assertEqual(
            payload["component_tests"]["metric_tetrad_component"]["variation_parity"],
            "even",
        )
        self.assertEqual(
            payload["component_tests"]["extrinsic_tetrad_component"]["variation_parity"],
            "odd",
        )
        self.assertFalse(payload["closure"]["R_h_ab_Z2_odd_coefficient_parity_proved"])
        self.assertFalse(payload["closure"]["R_K_ab_Z2_even_coefficient_parity_proved"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "R_h_ab_Z2_odd_coefficient_parity")


if __name__ == "__main__":
    unittest.main()
