from __future__ import annotations

import unittest

from scripts.build_p0_eft_radion_amplitude_closure import build_payload, solve_lambda_j


class P0EFTRadionAmplitudeClosureTests(unittest.TestCase):
    def test_lambda_j_is_solved_from_background_equation(self) -> None:
        closure = solve_lambda_j()

        self.assertIn("rho_dS", closure["Lambda_J_solution"])
        self.assertIn("cosh", closure["Lambda_J_solution"])

    def test_origin_branch_is_degenerate(self) -> None:
        closure = solve_lambda_j()

        self.assertIn("chi_inf=0", closure["degenerate_origin"])
        self.assertIn("cannot source dS", closure["degenerate_origin"])

    def test_full_no_fit_waits_for_background_data(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["Lambda_J_solved_algebraically"])
        self.assertFalse(status["chi_inf_fixed_by_Janus_background"])
        self.assertFalse(status["rho_dS_residual_fixed"])
        self.assertFalse(status["potential_fully_fixed_no_fit"])

    def test_obligations_name_two_remaining_background_inputs(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("rho_dS_residual", obligations)
        self.assertIn("chi_inf", obligations)


if __name__ == "__main__":
    unittest.main()
