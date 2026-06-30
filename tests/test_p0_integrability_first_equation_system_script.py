from __future__ import annotations

import unittest

from scripts.build_p0_integrability_first_equation_system import build_payload, render_markdown


class P0IntegrabilityFirstEquationSystemTests(unittest.TestCase):
    def test_artifact_is_open_bounded_and_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "integrability-first-equation-system-open")
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertFalse(payload["prediction_claim"])
        self.assertFalse(payload["fit_to_observations"])
        self.assertTrue(payload["regular_patch_toy_solver_available"])

    def test_unknowns_include_requested_blocks(self) -> None:
        symbols = {row["symbol"] for row in build_payload()["unknowns"]}

        self.assertIn("phi", symbols)
        self.assertIn("L/F_alpha", symbols)
        self.assertIn("u_to", symbols)
        self.assertIn("B_4vol", symbols)

    def test_equations_include_integrability_inverse_lorentz_and_caustic_gates(self) -> None:
        equations = {row["name"]: row for row in build_payload()["equations"]}
        text = " ".join(row["formula"] for row in equations.values())

        self.assertIn("D_alpha(B_4vol rho u_to^alpha)=0", text)
        self.assertIn("d(u_flat_to)=0", text)
        self.assertIn("projected_vorticity", text)
        self.assertIn("phi o phi^{-1}=id", text)
        self.assertIn("L^T eta L=eta", text)
        self.assertIn("same phi and L/F_alpha", text)
        self.assertIn("det(d phi) != 0", text)
        self.assertEqual(equations["caustic_exclusion"]["status"], "regularity-assumption")

    def test_count_states_not_solved_no_uniqueness_and_required_data(self) -> None:
        count = build_payload()["count"]

        self.assertEqual(count["unknown_blocks"], 4)
        self.assertEqual(count["equation_blocks"], 7)
        self.assertFalse(count["solves_equations"])
        self.assertFalse(count["proves_uniqueness"])
        self.assertTrue(count["requires_boundary_data"])
        self.assertTrue(count["requires_gauge_fixing"])

    def test_markdown_reports_prediction_false_and_limitations(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction claim: False", markdown)
        self.assertIn("Equations are stated as a calculable system, not solved.", markdown)
        self.assertIn("Uniqueness is not proved.", markdown)
        self.assertIn("Boundary or initial data are required.", markdown)
        self.assertIn("Gauge choices for phi and L/F_alpha are required.", markdown)


if __name__ == "__main__":
    unittest.main()
