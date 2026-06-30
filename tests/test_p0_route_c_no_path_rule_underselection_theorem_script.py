from __future__ import annotations

import unittest

from scripts.build_p0_route_c_no_path_rule_underselection_theorem import (
    build_payload,
    render_markdown,
)


class P0RouteCNoPathRuleUnderselectionTheoremTests(unittest.TestCase):
    def test_bounded_underselection_theorem_is_closed_without_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "no-path-rule-underselection-theorem-bounded")
        self.assertTrue(payload["lorentz_curvature_local_checks_pass"])
        self.assertTrue(payload["small_loop_checks_pass"])
        self.assertTrue(payload["two_path_counterexample_active"])
        self.assertFalse(payload["boundary_gauge_selects_zero_axiom_l"])
        self.assertFalse(payload["janus_path_rule_supplied"])
        self.assertFalse(payload["curvature_lorentz_holonomy_mirror_sufficient_for_unique_l"])
        self.assertTrue(payload["path_rule_required_for_unique_l"])
        self.assertTrue(payload["bounded_no_go_closed"])
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_theorem_rows_cover_required_premises(self) -> None:
        premises = {row["premise"] for row in build_payload()["theorem_rows"]}

        self.assertEqual(
            premises,
            {
                "lorentz_admissibility",
                "small_loop_holonomy",
                "noncommuting_holonomy",
                "mirror_boundary_structure",
                "pt_geometry_filter",
                "janus_path_source",
            },
        )

    def test_markdown_reports_path_rule_requirement(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Underselection Theorem", markdown)
        self.assertIn("Path rule required for unique L: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
