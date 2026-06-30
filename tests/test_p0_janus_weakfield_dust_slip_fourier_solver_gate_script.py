from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_dust_slip_fourier_solver_gate import (
    build_payload,
    determinant_factor,
    fourier_matrix,
    render_markdown,
)


class P0JanusWeakfieldDustSlipFourierSolverGateTests(unittest.TestCase):
    def test_fourier_matrix_has_expected_coupled_rows(self) -> None:
        matrix = fourier_matrix()

        self.assertEqual(matrix.shape, (2, 2))
        self.assertIn("rho0_minus_to_plus", sp.sstr(matrix[0, 0]))
        self.assertIn("rho0_plus_to_minus", sp.sstr(matrix[1, 0]))

    def test_determinant_factorization_is_exact(self) -> None:
        self.assertEqual(determinant_factor(), 0)

    def test_payload_records_invertibility_but_not_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-slip-fourier-solver-gate-open")
        self.assertTrue(payload["fourier_solver_written"])
        self.assertIn("k2 != 0", " ".join(payload["invertibility_conditions"]))
        self.assertTrue(payload["zero_mode_requires_boundary_gauge"])
        self.assertTrue(payload["mass_gap_resonance_requires_source_branch"])
        self.assertFalse(payload["background_branch_selected"])
        self.assertFalse(payload["boundary_conditions_source_derived"])
        self.assertFalse(payload["qdet_convention_selected_from_source"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_solution_keeps_source_symbols(self) -> None:
        payload = build_payload()

        self.assertIn("S_plus", payload["solution_psi_plus"])
        self.assertIn("S_minus", payload["solution_psi_minus"])
        self.assertIn("rho0_minus_to_plus", payload["solution_psi_plus"])

    def test_markdown_lists_open_modes(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Zero mode requires boundary/gauge: True", markdown)
        self.assertIn("Mass-gap resonance requires source branch: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
