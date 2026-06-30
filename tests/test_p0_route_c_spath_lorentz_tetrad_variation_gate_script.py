from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_lorentz_tetrad_variation_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCSpathLorentzTetradVariationGateTests(unittest.TestCase):
    def test_lorentz_variation_is_formalized_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-lorentz-tetrad-variation-formal-open")
        self.assertTrue(payload["lorentz_constrained_variation_formalized"])
        self.assertTrue(payload["first_order_lorentz_constraint_preserved"])
        self.assertTrue(payload["eta_lorentz_projector_verified"])
        self.assertTrue(payload["tetrad_bridge_formula_written"])
        self.assertFalse(payload["full_tensor_el_closed"])
        self.assertFalse(payload["same_l_stack_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_variation_rows_cover_constraint_projector_spin_and_tetrad(self) -> None:
        rows = {row["object"]: row for row in build_payload()["variation_rows"]}

        self.assertEqual(
            set(rows),
            {
                "admissible_variation",
                "constraint_preservation",
                "projected_el_equation",
                "spin_covariant_residual",
                "tetrad_bridge",
            },
        )
        self.assertTrue(all(row["formalized"] for row in rows.values()))
        self.assertTrue(all(not row["closed_for_prediction"] for row in rows.values()))

    def test_projector_and_constraint_residuals_are_zero(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["xi_eta_residual"], "Matrix([[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])")
        self.assertEqual(
            payload["projected_generic_matrix_eta_residual"],
            "Matrix([[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])",
        )

    def test_markdown_reports_open_physics(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Lorentz/Tetrad Variation", markdown)
        self.assertIn("First-order Lorentz constraint preserved: True", markdown)
        self.assertIn("Full tensor EL closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
