from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_delta_s00_measure_convention_gate import (
    build_payload,
    convention_expressions,
    render_markdown,
    symbols,
)


class P0JanusWeakfieldDeltaS00MeasureConventionGateTests(unittest.TestCase):
    def test_proper_and_effective_conventions_are_equivalent_by_definition(self) -> None:
        s = symbols()
        expressions = convention_expressions()

        substituted_effective = expressions["effective_cross_delta"].subs(
            s["delta_rho_other_eff"],
            expressions["effective_density_definition"],
        )

        self.assertEqual(
            sp.simplify(substituted_effective - expressions["proper_cross_delta"]),
            0,
        )

    def test_double_counting_residual_is_one_extra_b4vol_response(self) -> None:
        s = symbols()
        expressions = convention_expressions()

        self.assertEqual(
            expressions["double_counting_residual"],
            s["delta_rho_other_eff"] - s["delta_rho_other_proper"],
        )
        residual_after_definition = expressions["double_counting_residual"].subs(
            s["delta_rho_other_eff"],
            expressions["effective_density_definition"],
        )
        self.assertEqual(
            sp.simplify(residual_after_definition),
            s["rho0_other_to_self"] * s["delta_B"],
        )

        extra_if_effective_is_already_expanded = sp.simplify(
            expressions["double_counted_cross_delta"].subs(
                s["delta_rho_other_eff"],
                expressions["effective_density_definition"],
            )
            - expressions["proper_cross_delta"]
        )
        self.assertEqual(extra_if_effective_is_already_expanded, s["rho0_other_to_self"] * s["delta_B"])

    def test_payload_rejects_double_counted_branch(self) -> None:
        payload = build_payload()
        rows = {row["name"]: row for row in payload["convention_rows"]}

        self.assertEqual(payload["status"], "delta-s00-measure-convention-algebra-closed-selection-open")
        self.assertTrue(payload["measure_convention_algebra_closed"])
        self.assertTrue(payload["single_active_convention_required"])
        self.assertEqual(payload["selected_field_residual_branch"], "field_equation_4volume_source")
        self.assertEqual(payload["selected_field_residual_convention"], "proper_density_input")
        self.assertTrue(payload["field_residual_convention_selected"])
        self.assertIsNone(payload["accepted_convention"])
        self.assertFalse(payload["source_convention_selected"])
        self.assertTrue(payload["double_counting_forbidden"])
        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertTrue(rows["proper_density_input"]["accepted_for_delta_s00_algebra"])
        self.assertTrue(rows["effective_density_input"]["accepted_for_delta_s00_algebra"])
        self.assertFalse(rows["double_counted_effective_times_b4vol"]["accepted_for_delta_s00_algebra"])

    def test_no_fit_or_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_forbidden_double_counting(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Delta S00 Measure Convention", markdown)
        self.assertIn("Selected field residual convention: `proper_density_input`", markdown)
        self.assertIn("Field residual convention selected: True", markdown)
        self.assertIn("Double counting forbidden: True", markdown)
        self.assertIn("Qdet absorption allowed: False", markdown)
        self.assertIn("double_counted_effective_times_b4vol", markdown)


if __name__ == "__main__":
    unittest.main()
