from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_dust_slip_poisson_target import (
    build_payload,
    coupled_poisson_residuals,
    dust_delta_b4vol_minus_from_plus,
    dust_delta_b4vol_plus_from_minus,
    render_markdown,
)


class P0JanusWeakfieldDustSlipPoissonTargetTests(unittest.TestCase):
    def test_dust_slip_b4vol_is_reciprocal(self) -> None:
        self.assertEqual(sp.simplify(dust_delta_b4vol_plus_from_minus() + dust_delta_b4vol_minus_from_plus()), 0)

    def test_coupled_poisson_rows_keep_background_feedback(self) -> None:
        payload = build_payload()
        rows = " ".join(row["residual_zero_form"] for row in payload["operator_rows"])

        self.assertIn("rho0_minus_to_plus", rows)
        self.assertIn("rho0_plus_to_minus", rows)
        self.assertIn("Psi_minus - Psi_plus", rows)

    def test_relative_row_matches_subtracted_sector_rows(self) -> None:
        residuals = coupled_poisson_residuals()
        self.assertIn("Lap_Psi_minus", sp.sstr(residuals["relative"]))
        self.assertIn("S_minus", sp.sstr(residuals["relative"]))
        self.assertIn("rho0_minus_to_plus - rho0_plus_to_minus", sp.sstr(residuals["relative"]))

    def test_target_is_conditional_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dust-slip-coupled-poisson-target-open")
        self.assertTrue(payload["dust_slip_condition_applied_conditionally"])
        self.assertTrue(payload["coupled_operator_written"])
        self.assertFalse(payload["background_branch_selected"])
        self.assertFalse(payload["boundary_conditions_source_derived"])
        self.assertFalse(payload["qdet_convention_selected_from_source"])
        self.assertFalse(payload["same_l_qcross_selected"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_lists_assumptions_and_open_gates(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("zero effective anisotropic stress", markdown)
        self.assertIn("Background branch selected: False", markdown)
        self.assertIn("Q_det convention selected from source: False", markdown)


if __name__ == "__main__":
    unittest.main()
