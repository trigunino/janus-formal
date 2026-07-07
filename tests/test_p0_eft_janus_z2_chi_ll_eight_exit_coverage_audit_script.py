import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_eight_exit_coverage_audit import build_payload


class ChiLLEightExitCoverageAuditTests(unittest.TestCase):
    def test_all_eight_exits_have_frontiers(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["all_eight_have_frontier_gate_or_imported_frontier"])
        self.assertEqual(len(payload["exits"]), 8)

    def test_no_exit_is_ready_in_current_workspace(self):
        payload = build_payload()

        self.assertFalse(payload["chi_LL_prediction_ready"])
        self.assertEqual(payload["ready_exits"], [])

    def test_expected_exit_names_are_present(self):
        exits = build_payload()["exits"]

        self.assertEqual(
            set(exits),
            {
                "area_gap_exit",
                "spin_condensate_exit",
                "UV_LL_action_exit",
                "state_charge_exit",
                "horizon_thermodynamic_exit",
                "spectral_stability_exit",
                "Casimir_topological_exit",
                "regularity_global_closure_exit",
            },
        )


if __name__ == "__main__":
    unittest.main()
