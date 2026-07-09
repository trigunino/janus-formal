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
            payload["aps_pin"]["frontier_gate"],
            "p0_eft_janus_z4_hard_global_atomic_frontier_gate",
        )
        self.assertEqual(
            payload["orbifold_2_to_1"]["refined_gate"],
            "p0_eft_janus_z4_orbifold_cover_ratio_obligation_gate",
        )
        self.assertEqual(
            payload["orbifold_2_to_1"]["frontier_gate"],
            "p0_eft_janus_z4_hard_global_atomic_frontier_gate",
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
            payload["unique_action"]["target"],
            "unique Janus Z2/Sigma/Holst action-to-equations derivation",
        )
        self.assertEqual(
            payload["hard_external_theorem_target_registry"],
            "p0_eft_janus_z4_hard_external_theorem_target_registry",
        )
        self.assertEqual(
            payload["topology_layer_alignment"]["gate"],
            "p0_eft_janus_topology_layer_alignment_gate",
        )
        self.assertEqual(
            payload["topology_layer_alignment"]["projective_tunnel_interface_gate"],
            "p0_eft_janus_projective_tunnel_interface",
        )
        self.assertEqual(payload["topology_layer_alignment"]["topological_cover_group"], "Z2")
        self.assertTrue(payload["topology_layer_alignment"]["projective_tunnel_closed"])
        self.assertTrue(payload["topology_layer_alignment"]["around_sigma_cycle_transport_available"])
        self.assertEqual(payload["topology_layer_alignment"]["natural_four_sector_group"], "Z2xZ2")
        self.assertFalse(payload["topology_layer_alignment"]["cyclic_z4_monodromy_proved"])
        self.assertFalse(payload["topology_layer_alignment"]["cyclic_z4_inference_allowed"])
        self.assertEqual(payload["topology_layer_alignment"]["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["topology_layer_alignment"]["z4_cmb_marked_non_evidence"])
        self.assertEqual(
            payload["topology_layer_alignment"]["rp4_pin_sign_audit_gate"],
            "p0_eft_janus_rp4_pin_sign_audit_gate",
        )
        self.assertEqual(
            payload["topology_layer_alignment"]["projective_tunnel_cover_ratio_gate"],
            "p0_eft_janus_projective_tunnel_cover_ratio_gate",
        )
        self.assertEqual(
            payload["topology_layer_alignment"]["sigma_boundary_action_support_gate"],
            "p0_eft_janus_sigma_boundary_action_support_gate",
        )
        self.assertTrue(payload["topology_layer_alignment"]["rp4_pin_sign_recheck_required"])
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
