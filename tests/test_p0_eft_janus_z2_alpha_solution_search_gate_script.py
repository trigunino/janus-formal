import unittest

from scripts.build_p0_eft_janus_z2_alpha_solution_search_gate import build_payload


class AlphaSolutionSearchGateTests(unittest.TestCase):
    def test_search_selects_state_conditional_solution(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["best_current_solution"],
            "exact_solution_integration_constant_state_sector",
        )
        self.assertTrue(payload["alpha_may_be_supplied_as_state_sector"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])

    def test_pure_topology_does_not_fix_dimensionful_alpha(self):
        payload = build_payload()

        self.assertFalse(payload["pure_topology_can_fix_alpha"])
        self.assertIn("pure_topology_RP4_Sigma_Z2", payload["no_go_routes"])


if __name__ == "__main__":
    unittest.main()
