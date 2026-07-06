import unittest

from scripts.derive_p0_eft_janus_z2_sigma_no_extension_frontier_summary_gate import (
    build_payload,
)


class JanusZ2SigmaNoExtensionFrontierSummaryGateTest(unittest.TestCase):
    def test_frontier_records_remaining_no_extension_blockers(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["policy"]["extension_allowed"])
        self.assertFalse(payload["full_no_fit_prediction_ready"])
        self.assertTrue(
            payload["no_extension_route_exhausted_for_observational_BAO"]
        )
        self.assertTrue(payload["blockers"]["R_Sigma_modulus"]["open"])
        self.assertTrue(payload["blockers"]["R_Sigma_modulus"]["relative_ratio_fixed"])
        self.assertTrue(payload["blockers"]["R_Sigma_modulus"]["absolute_scale_open"])
        self.assertTrue(payload["blockers"]["projected_baryon_charge"]["open"])
        self.assertIn(
            "R_Sigma_not_fixed_by_existing_action", payload["primary_blockers"]
        )
        self.assertIn(
            "superselection_state_or_initial_occupation_not_fixed",
            payload["primary_blockers"],
        )
        routes = payload["no_extension_routes_tested"]
        self.assertTrue(routes["collar_reduction_to_surface_Rh"]["operator_found"])
        self.assertFalse(routes["collar_reduction_to_surface_Rh"]["coefficient_fixed"])
        self.assertFalse(routes["regular_throat_condition"]["R_Sigma_fixed"])
        self.assertTrue(routes["global_regular_round_product_probe"]["F_reg_flat_zero"])
        self.assertFalse(routes["global_regular_round_product_probe"]["R_Sigma_fixed"])
        self.assertTrue(
            routes["global_regular_deck_twist_probe"]["F_reg_constant_nonzero"]
        )
        self.assertFalse(routes["global_regular_deck_twist_probe"]["R_Sigma_fixed"])
        self.assertTrue(routes["homothetic_collar_class"]["lambda_independent_F_reg"])
        self.assertFalse(routes["homothetic_collar_class"]["R_Sigma_fixed"])
        self.assertTrue(
            routes["reciprocal_projective_collar_probe"]["candidate_ratio_found"]
        )
        self.assertEqual(routes["reciprocal_projective_collar_probe"]["candidate_ratio"], 1.0)
        self.assertFalse(routes["reciprocal_projective_collar_probe"]["R_Sigma_fixed"])
        self.assertTrue(routes["projective_stereographic_ratio_solution"]["ratio_solution_ready"])
        self.assertEqual(
            routes["projective_stereographic_ratio_solution"]["R_Sigma_over_ell_collar"],
            1.0,
        )
        self.assertFalse(
            routes["projective_stereographic_ratio_solution"]["absolute_R_Sigma_fixed"]
        )
        self.assertTrue(
            routes["effective_partial_closure_from_projective_ratio"][
                "partial_effective_closure_ready"
            ]
        )
        self.assertFalse(
            routes["effective_partial_closure_from_projective_ratio"][
                "effective_closure_ready"
            ]
        )
        self.assertEqual(
            routes["effective_partial_closure_from_projective_ratio"][
                "R_Sigma_over_ell_collar_Z2Sigma"
            ],
            1.0,
        )
        self.assertEqual(
            routes["effective_partial_closure_from_projective_ratio"][
                "primary_blocker"
            ],
            "superselection_state_or_initial_occupation_not_fixed",
        )
        self.assertTrue(
            routes["APS_Pin_projected_charge_selection"][
                "charge_class_constraints_found"
            ]
        )
        self.assertFalse(
            routes["APS_Pin_projected_charge_selection"]["absolute_charge_fixed"]
        )
        self.assertTrue(routes["Z2_cover_bianchi_balance"]["projected_equations_ready"])
        self.assertTrue(routes["Z2_cover_bianchi_balance"]["measure_transport_ready"])
        self.assertTrue(routes["Z2_cover_bianchi_balance"]["paired_bianchi_balance_ready"])
        self.assertFalse(routes["Z2_cover_bianchi_balance"]["paired_bianchi_closed"])
        self.assertIn("missing_bianchi_balance_or_sigma_source", payload["primary_blockers"])


if __name__ == "__main__":
    unittest.main()
