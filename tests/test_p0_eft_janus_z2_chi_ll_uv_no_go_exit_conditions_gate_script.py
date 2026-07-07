import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_uv_no_go_exit_conditions_gate import build_payload


class ChiLLUVNoGoExitConditionsGateTests(unittest.TestCase):
    def test_current_workspace_satisfies_no_go(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["no_go_holds_for_current_workspace"])
        self.assertFalse(payload["chi_LL_prediction_ready"])

    def test_forbidden_shortcuts_are_explicit(self):
        shortcuts = build_payload()["forbidden_shortcuts"]

        self.assertTrue(shortcuts["set_Rs_equal_lP_by_choice"])
        self.assertTrue(shortcuts["use_Holst_gamma_as_length"])
        self.assertTrue(shortcuts["fit_chi_LL_to_H0_or_BAO"])

    def test_search_space_is_reduced_to_four_exits(self):
        exits = build_payload()["admissible_non_rustine_exits"]

        self.assertEqual(
            set(exits),
            {"area_gap_exit", "spin_condensate_exit", "UV_LL_action_exit", "state_charge_exit"},
        )
        self.assertFalse(any(exit_data["ready"] for exit_data in exits.values()))


if __name__ == "__main__":
    unittest.main()
