from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_solver_ec_branch import build_payload, render_markdown


class P0EFTGrowthSolverECBranchTests(unittest.TestCase):
    def test_mu_closed_but_growth_inputs_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["mu_iso_EC_branch_closed"])
        self.assertTrue(status["growth_solver_equations_closed_symbolically"])
        self.assertFalse(status["Omega_torsion_unit_background_specified"])
        self.assertFalse(status["S_kink_numeric_or_symbolic_closed"])
        self.assertFalse(status["fsigma8_curve_generated"])

    def test_mu_limits_are_recorded(self) -> None:
        mu = build_payload()["mu"]

        self.assertIn("161/36", mu["alpha_iso"])
        self.assertIn("mu -> 1", mu["ir_limit"])
        self.assertIn("161/36", mu["uv_limit"])

    def test_solver_requires_background_inputs(self) -> None:
        solver = build_payload()["solver"]

        self.assertIn("Omega_torsion_unit(a)", solver["ready_to_integrate"])
        self.assertIn("S_kink", solver["ready_to_integrate"])

    def test_markdown_keeps_full_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("mu_iso_EC_branch_closed: True", markdown)
        self.assertIn("full_cosmology_prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
