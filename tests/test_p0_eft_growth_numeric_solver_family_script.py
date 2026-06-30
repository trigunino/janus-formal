from __future__ import annotations

import unittest

from scripts.build_p0_eft_growth_numeric_solver_family import build_payload, render_markdown


class P0EFTGrowthNumericSolverFamilyTests(unittest.TestCase):
    def test_solver_family_ready_but_not_final_prediction(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["numeric_solver_family_specified"])
        self.assertTrue(status["piecewise_kick_integration_specified"])
        self.assertTrue(status["fsigma8_family_ready"])
        self.assertFalse(status["Omega_torsion_background_derived_from_Janus"])
        self.assertFalse(status["S_kink_amplitude_derived"])
        self.assertFalse(status["fsigma8_prediction_no_fit_ready"])

    def test_profile_is_parametric_and_marked_not_final(self) -> None:
        omega = build_payload()["omega_torsion"]

        self.assertIn("Omega_T0", omega["profile_family"])
        self.assertIn("not-final", omega["status"])

    def test_solver_has_piecewise_kick(self) -> None:
        solver = build_payload()["solver"]

        self.assertIn("X2_+", solver["kick"])
        self.assertIn("piecewise", solver["integration"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("fsigma8_family_ready: True", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
