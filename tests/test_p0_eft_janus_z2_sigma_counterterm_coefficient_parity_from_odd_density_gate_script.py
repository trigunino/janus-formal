import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_coefficient_parity_from_odd_density_gate import (
    build_payload,
)


class CountertermCoefficientParityFromOddDensityGateTests(unittest.TestCase):
    def test_conditional_parity_derivation_is_ready_but_odd_density_blocks(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(
            payload["conditional_derivation"]["if_L_ct_Z2_odd_then_R_h_ab_Z2_odd"]
        )
        self.assertTrue(
            payload["conditional_derivation"]["if_L_ct_Z2_odd_then_R_K_ab_Z2_even"]
        )
        self.assertFalse(payload["closure"]["L_ct_Z2_odd_density_proved"])
        self.assertFalse(payload["closure"]["R_h_ab_Z2_odd_coefficient_parity_proved"])
        self.assertFalse(payload["closure"]["R_K_ab_Z2_even_coefficient_parity_proved"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["primary_blocker"], "L_ct_Z2_odd_density")
        self.assertEqual(
            payload["upstream_frontiers"]["L_ct_Z2_odd_density"]["primary_blocker"],
            "alpha_res_Z2_anti_invariance",
        )
        self.assertIn("tau_Z2^* R_h_ab", payload["formulae"]["result_R_h"])
        self.assertIn("tau_Z2^* R_K_ab", payload["formulae"]["result_R_K"])


if __name__ == "__main__":
    unittest.main()
