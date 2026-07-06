import unittest

from scripts.build_p0_eft_janus_z2_sigma_plugstar_ejection_threshold_gate import (
    build_payload,
)


class PlugstarEjectionThresholdGateTests(unittest.TestCase):
    def test_plugstar_route_has_conditional_threshold_solution_waiting_for_active_a_k(self):
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
        self.assertEqual(payload["route_status"], "conditional_closed_waiting_for_active_A_K")
        self.assertEqual(payload["primary_blocker"], "none")
        self.assertFalse(payload["active_A_K_status"]["gate_passed"])
        self.assertIsNone(payload["active_threshold_solution"])
        self.assertTrue(payload["archive_decision"]["archive_ready"])
        self.assertFalse(payload["archive_decision"]["active_pipeline_promotion_allowed"])
        self.assertTrue(
            payload["archive_decision"]["active_pipeline_import_forbidden_until_A_K_ready"]
        )
        self.assertEqual(
            payload["archive_decision"]["final_verdict"],
            "useful_as_minimum_throat_constraint_not_active_closure",
        )
        self.assertIn("R_Sigma_min", payload["mechanism"]["target_constraint"])
        self.assertEqual(
            payload["threshold_solution"]["solution"],
            "R_Sigma_min = sqrt(A_K) / K_crit",
        )
        self.assertTrue(payload["candidate_thresholds"]["curvature_threshold"]["can_bound_radius"])

    def test_plugstar_route_uses_active_a_k_when_certificate_ready(self):
        active_a_k = {
            "status": "janus-z2-sigma-plugstar-curvature-amplitude-from-embedding-gate",
            "gate_passed": True,
            "route_status": "active_A_K_derived",
            "primary_blocker": "none",
            "active_A_K_certificate": {"A_K": 63.0},
            "threshold_solution": {
                "equation": "A_K / R_Sigma^2 = K_crit^2",
                "A_K": 63.0,
                "R_Sigma_min": "sqrt(A_K) / K_crit",
                "active_bound": "R_Sigma(a) >= sqrt(63) / K_crit",
            },
            "next_required": [],
        }

        payload = build_payload(active_a_k_payload=active_a_k)

        self.assertEqual(payload["route_status"], "active_bound_ready")
        self.assertTrue(payload["active_A_K_status"]["gate_passed"])
        self.assertEqual(payload["active_threshold_solution"]["A_K"], 63.0)
        self.assertTrue(payload["archive_decision"]["active_pipeline_promotion_allowed"])
        self.assertFalse(
            payload["archive_decision"]["active_pipeline_import_forbidden_until_A_K_ready"]
        )
        self.assertEqual(payload["next_required"], [])


if __name__ == "__main__":
    unittest.main()
