import unittest

from scripts.build_p0_eft_janus_z2_sigma_point_collapse_limit_gate import build_payload


class SigmaPointCollapseLimitGateTests(unittest.TestCase):
    def test_point_collapse_route_is_isolated_and_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["route"], "SigmaPointCollapseLimitGate")
        self.assertEqual(payload["source"], "exploratory_branch_only")
        self.assertTrue(payload["declared"]["point_collapse_route_declared"])
        self.assertTrue(payload["declared"]["active_pipeline_replacement_forbidden"])
        self.assertTrue(payload["closure"]["volume_collapse_rate_declared"])
        self.assertFalse(payload["closure"]["alpha_res_growth_bound_declared"])
        self.assertFalse(payload["closure"]["distributional_defect_control_declared"])
        self.assertFalse(payload["closure"]["integrated_alpha_res_vanishes_proved"])
        self.assertFalse(payload["closure"]["L_ct_bypass_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["route_status"], "credible_but_blocked")
        self.assertEqual(payload["primary_blocker"], "alpha_res_growth_bound_declared")
        self.assertFalse(
            payload["scaling_channels"]["cubic_or_delta_slot"][
                "vanishes_if_bound_uniform"
            ]
        )
        self.assertIn("R_Sigma -> 0", payload["limit_formula"]["target"])


if __name__ == "__main__":
    unittest.main()
