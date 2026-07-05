import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_lct_expression_obstruction_gate import (
    build_payload,
)


class CountertermLctExpressionObstructionGateTests(unittest.TestCase):
    def test_blocks_expression_without_explicit_residual_one_form(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["S_ct_boundary_action_available"])
        self.assertTrue(payload["variational_formula_available"])
        self.assertTrue(payload["alpha_res_partial_written"])
        self.assertFalse(payload["residual_one_form_explicit"])
        self.assertFalse(payload["L_ct_expression_derivable_now"])
        self.assertFalse(payload["counterterm_local_density_action_inputs_written"])
        self.assertEqual(payload["primary_blocker"], "explicit_residual_one_form_alpha_res")
        self.assertIn("choose alpha/beta ansatz for L_ct", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
