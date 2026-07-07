import unittest

from scripts.build_p0_eft_janus_z2_sigma_pt67_generalized_bc_coefficient_solver_gate import (
    build_payload,
)


class PT67GeneralizedBCCoefficientSolverGateTests(unittest.TestCase):
    def test_strict_no_extension_fixes_all_generalized_bc_coefficients_to_zero(self):
        payload = build_payload()
        result = payload["result"]

        self.assertTrue(result["linear_K_duplicate_forbidden"])
        self.assertTrue(result["remaining_non_GHY_residual_absent"])
        self.assertTrue(result["all_generalized_BC_coefficients_fixed"])
        self.assertTrue(result["generalized_boundary_action_trivial_under_strict_no_extension"])
        self.assertEqual(
            result["constraints"],
            {
                "lambda_K": 0.0,
                "lambda_0": 0.0,
                "lambda_R3": 0.0,
                "lambda_K2": 0.0,
                "lambda_Kab2": 0.0,
            },
        )


if __name__ == "__main__":
    unittest.main()
