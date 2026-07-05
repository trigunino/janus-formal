import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_coefficient_expansion_obligation_gate import (
    build_payload,
)


class CountertermCoefficientExpansionObligationGateTests(unittest.TestCase):
    def test_blocks_density_inputs_until_metric_and_k_coefficients_exist(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["boundary_action_functional_closed"])
        self.assertTrue(payload["known_partial_closures"]["R_T_A_ready"])
        self.assertTrue(payload["known_partial_closures"]["R_chi_partial_R_chi_ready"])
        self.assertFalse(payload["explicit_coefficient_expansion_ready"])
        self.assertFalse(payload["counterterm_local_density_action_inputs_allowed"])
        self.assertTrue(payload["variational_coefficient_formula_closed"])
        self.assertEqual(payload["primary_blocker"], "explicit_L_ct_expression")
        self.assertFalse(payload["lct_expression_obstruction"]["L_ct_expression_derivable_now"])
        self.assertEqual(
            payload["lct_expression_obstruction"]["primary_blocker"],
            "explicit_residual_one_form_alpha_res",
        )
        self.assertIn("partial L_ct/partial h_ab", payload["coefficient_formulas"]["R_h_ab"])
        ready = {row["coefficient"]: row["ready"] for row in payload["coefficient_rows"]}
        self.assertFalse(ready["R_h_ab"])
        self.assertFalse(ready["R_K_ab"])
        self.assertTrue(ready["R_T_A"])
        self.assertIn("derive_explicit_L_ct_expression_in_allowed_basis", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
