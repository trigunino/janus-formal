from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_constraint_equation_classifier import (
    build_payload,
    render_markdown,
)


class P0RouteCSPathConstraintEquationClassifierTests(unittest.TestCase):
    def test_available_constraints_are_filters(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-constraint-equation-classifier-open")
        self.assertFalse(payload["pt_is_equation"])
        self.assertFalse(payload["same_l_is_equation"])
        self.assertFalse(payload["stability_is_equation"])
        self.assertFalse(payload["weak_field_sign_is_equation"])
        self.assertFalse(payload["source_action_el_available"])
        self.assertTrue(payload["all_available_constraints_are_filters"])
        self.assertFalse(payload["unique_selector_available"])
        self.assertFalse(payload["prediction_ready"])

    def test_classifier_rows_cover_pt_samel_stability_and_source(self) -> None:
        rows = {row["constraint"]: row for row in build_payload()["classifier_rows"]}

        self.assertEqual(
            set(rows),
            {"PT_parity", "same_L", "stability", "weak_field_sign", "source_action_EL"},
        )
        self.assertTrue(all(not row["selects_unique"] for row in rows.values()))
        self.assertEqual(rows["stability"]["class"], "inequality_filter")
        self.assertEqual(rows["source_action_EL"]["class"], "missing_equation")

    def test_markdown_reports_classifier_result(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Constraint Equation Classifier", markdown)
        self.assertIn("PT is equation: False", markdown)
        self.assertIn("All available constraints are filters: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
