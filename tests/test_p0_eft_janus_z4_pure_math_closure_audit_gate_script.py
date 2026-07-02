import unittest

from scripts.build_p0_eft_janus_z4_pure_math_closure_audit_gate import build_payload


class P0EFTJanusZ4PureMathClosureAuditGateTests(unittest.TestCase):
    def test_audit_keeps_no_fit_false_until_global_theorems_are_axiom_free(self):
        payload = build_payload()

        self.assertTrue(payload["aps_pin"]["scaffold_complete"])
        self.assertTrue(payload["orbifold_2_to_1"]["scaffold_complete"])
        self.assertTrue(payload["unique_action"]["scaffold_complete"])
        self.assertEqual(
            payload["aps_pin"]["refined_gate"],
            "p0_eft_janus_z4_aps_index_package_obligation_gate",
        )
        self.assertEqual(
            payload["orbifold_2_to_1"]["refined_gate"],
            "p0_eft_janus_z4_orbifold_cover_ratio_obligation_gate",
        )
        self.assertIn(
            "p0_eft_janus_z4_nonlinear_el_residual_obligation_gate",
            payload["unique_action"]["refined_gates"],
        )
        self.assertIn(
            "p0_eft_janus_z4_gauge_fixing_variation_uniqueness_gate",
            payload["unique_action"]["refined_gates"],
        )
        self.assertEqual(
            payload["hard_external_theorem_target_registry"],
            "p0_eft_janus_z4_hard_external_theorem_target_registry",
        )
        self.assertFalse(payload["aps_pin"]["global_index_theorem_proved_without_axioms"])
        self.assertFalse(payload["orbifold_2_to_1"]["global_orbifold_theorem_proved_without_axioms"])
        self.assertFalse(payload["unique_action"]["unique_action_full_variation_proved_without_axioms"])
        self.assertIn(
            "global_euler_holonomy_class_computed",
            payload["orbifold_2_to_1"]["remaining_axioms"],
        )
        self.assertIn(
            "common_obstruction_vanishes",
            payload["unique_action"]["remaining_axioms"],
        )
        self.assertFalse(payload["pure_math_model_closed_without_axioms"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
