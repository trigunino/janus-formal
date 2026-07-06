import unittest

from scripts.build_p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate import (
    build_payload,
)


class PlugstarEjectionThresholdGateTests(unittest.TestCase):
    def test_plugstar_route_has_conditional_threshold_solution(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["route"], "SigmaPlugstarEjectionThresholdGate")
        self.assertEqual(payload["source"], "parallel_exploratory_branch_only")
        self.assertTrue(payload["declared"]["parallel_exploration_only"])
        self.assertTrue(payload["declared"]["active_pipeline_replacement_forbidden"])
        self.assertTrue(payload["declared"]["point_collapse_replaced_by_threshold_branch"])
        self.assertTrue(payload["closure"]["concentration_functional_declared"])
        self.assertTrue(payload["closure"]["ejection_branch_declared"])
        self.assertTrue(payload["closure"]["z2_threshold_invariant"])
        self.assertTrue(payload["closure"]["paired_opposite_sheet_ejection_declared"])
        self.assertTrue(payload["closure"]["z2_transmission_compatibility_declared"])
        self.assertTrue(payload["closure"]["threshold_equation_derived"])
        self.assertTrue(payload["closure"]["R_Sigma_min_bound_derived"])
        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["route_status"], "conditional_closed")
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertIn("R_Sigma_min", payload["mechanism"]["target_constraint"])
        self.assertEqual(
            payload["threshold_solution"]["solution"],
            "R_Sigma_min = sqrt(A_K) / K_crit",
        )
        self.assertTrue(payload["candidate_thresholds"]["curvature_threshold"]["can_bound_radius"])


if __name__ == "__main__":
    unittest.main()
