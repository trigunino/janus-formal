import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_minimal_basis_trace_constraints_gate import (
    build_payload,
)


class CountertermMinimalBasisTraceConstraintsGateTests(unittest.TestCase):
    def test_trace_constraints_do_not_fully_determine_coefficients(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["minimal_basis_imported"])
        self.assertIn("partial_R", payload["formulas"]["radial_E_counterterm"])
        self.assertIn(
            "6*epsilon_Z2*R/kappa_Z2Sigma",
            payload["formulas"]["cartan_plus_counterterm_balance"],
        )
        self.assertIn(
            "R_Sigma =",
            payload["formulas"]["formal_finite_radius_solution"],
        )
        self.assertFalse(payload["solvability"]["coefficients_fully_determined_by_minimal_basis"])
        self.assertEqual(payload["E_counterterm_zero_toy_solution"]["result"]["c1"], "0")
        self.assertEqual(
            payload["E_counterterm_zero_toy_solution"]["result"]["constraint"],
            "3*c2 + 2*c3 = 0",
        )
        self.assertEqual(payload["E_counterterm_zero_toy_solution"]["free_parameter"], "c2")
        self.assertIn("target_R_K_trace_function_or_boundary_condition", payload["solvability"]["minimum_new_inputs_needed"])
        self.assertIn(
            "then_promote_formal_finite_radius_solution_if_residual_zero",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
