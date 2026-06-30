from __future__ import annotations

import unittest

from scripts.build_p0_route_c_pt_geometry_path_rule_audit import (
    build_payload,
    render_markdown,
)


class P0RouteCPtGeometryPathRuleAuditTests(unittest.TestCase):
    def test_pt_geometry_filters_but_does_not_select_path_rule(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pt-geometry-path-rule-audit-open")
        self.assertFalse(payload["pt_geometry_source_found"])
        self.assertTrue(payload["pt_involution_filters_not_selects"])
        self.assertTrue(payload["pt_mirror_inverse_constraint"])
        self.assertTrue(payload["pt_lie_branch_filters_not_path_selector"])
        self.assertFalse(payload["pt_path_rule_selected"])
        self.assertTrue(payload["two_path_counterexample_survives_pt"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_pt_objects_and_extension_candidate(self) -> None:
        objects = {row["pt_object"] for row in build_payload()["rows"]}

        self.assertEqual(
            objects,
            {
                "pt_involution",
                "mirror_inverse_holonomy",
                "extended_poincare_lie_branch",
                "pt_fixed_surface_or_throat",
                "pt_paired_geodesics",
                "pt_wilson_line_candidate",
            },
        )

    def test_markdown_reports_no_zero_axiom_selector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("PT Geometry Path-Rule Audit", markdown)
        self.assertIn("PT path rule selected: False", markdown)
        self.assertIn("Two-path counterexample survives PT: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
