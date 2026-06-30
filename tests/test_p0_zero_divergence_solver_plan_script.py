from __future__ import annotations

import unittest

from scripts.build_p0_zero_divergence_solver_plan import build_payload


class P0ZeroDivergenceSolverPlanTests(unittest.TestCase):
    def test_solver_plan_is_actionable_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["source_pde_route"])
        self.assertTrue(payload["unknowns_declared"])
        self.assertTrue(payload["solver_branches_written"])
        self.assertFalse(payload["unique_solution_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_divergence_pde_and_lorentz_constraint(self) -> None:
        equations = " ".join(build_payload()["equations"])

        self.assertIn("D_plus_nu(B_4vol_plus_from_minus K_plus", equations)
        self.assertIn("D_minus_nu(B_4vol_minus_from_plus K_minus", equations)
        self.assertIn("Omega_{alpha AB}+Omega_{alpha BA}=0", equations)
        self.assertIn("Q_cross", equations)

    def test_solver_branches_cover_direct_transport_and_gauge(self) -> None:
        branches = {row["branch"] for row in build_payload()["solver_branches"]}

        self.assertIn("direct_divergence_pde_for_K", branches)
        self.assertIn("transported_matter_parameterization", branches)
        self.assertIn("minimal_norm_pde_gauge", branches)

    def test_closure_tests_keep_prediction_blocked(self) -> None:
        tests = " ".join(build_payload()["closure_tests"])
        next_artifacts = " ".join(build_payload()["next_artifacts"])

        self.assertIn("R_plus", tests)
        self.assertIn("R_minus", tests)
        self.assertIn("B_4vol product-rule", tests)
        self.assertIn("Newtonian/TOV", tests)
        self.assertIn("Pi", tests)
        self.assertIn("uniqueness/gauge audit", next_artifacts)


if __name__ == "__main__":
    unittest.main()
