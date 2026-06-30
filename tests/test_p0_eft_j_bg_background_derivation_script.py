from __future__ import annotations

import unittest

from scripts.build_p0_eft_j_bg_background_derivation import build_payload, solve_coupled_background


class P0EFTJBgBackgroundDerivationTests(unittest.TestCase):
    def test_jbg_is_background_trace_source(self) -> None:
        solution = solve_coupled_background()

        self.assertEqual(solution["J_bg"], "eps*rho/Mpl2")

    def test_coupled_solution_fixes_chi_and_lambda(self) -> None:
        solution = solve_coupled_background()

        self.assertIn("atanh", solution["chi_inf_solution"])
        self.assertIn("rho", solution["canonical_Lambda_J_solution"])

    def test_status_is_conditional_not_unconditional(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["amplitude_closed_conditionally"])
        self.assertFalse(status["unconditional_no_fit_ready"])

    def test_existence_condition_is_explicit(self) -> None:
        solution = solve_coupled_background()

        self.assertIn("|eps|", solution["existence_condition"])


if __name__ == "__main__":
    unittest.main()
