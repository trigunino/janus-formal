from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_bdefect_action_filter import build_payload, render_markdown


class P0OrbifoldPTBDefectActionFilterTests(unittest.TestCase):
    def test_filter_is_written_but_underselects(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-bdefect-action-filter-underselects")
        self.assertTrue(payload["b_defect_forms_written"])
        self.assertTrue(payload["topological_term_candidate_written"])
        self.assertTrue(payload["defect_tension_candidate_written"])
        self.assertTrue(payload["matter_solder_boundary_candidate_written"])
        self.assertTrue(payload["fit_boundary_rejected"])
        self.assertFalse(payload["unique_b_defect_selected"])
        self.assertFalse(payload["b_defect_source_derived"])
        self.assertFalse(payload["j_defect_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_candidate_classes(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["rows"]}

        self.assertEqual(
            set(rows),
            {
                "topological_boundary_term",
                "defect_tension_geometry",
                "matter_solder_boundary",
                "pt_constraint_multiplier",
                "gauge_breaking_mass",
                "observable_fit_boundary",
            },
        )
        self.assertTrue(rows["topological_boundary_term"]["yields_j_defect"])
        self.assertFalse(rows["defect_tension_geometry"]["yields_j_defect"])
        self.assertFalse(rows["observable_fit_boundary"]["accepted"])

    def test_admissible_and_rejected_sets_are_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("topological_boundary_term", payload["admissible_but_unaccepted"])
        self.assertIn("matter_solder_boundary", payload["admissible_but_unaccepted"])
        self.assertIn("gauge_breaking_mass", payload["rejected_candidates"])
        self.assertIn("observable_fit_boundary", payload["rejected_candidates"])

    def test_markdown_reports_no_selection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("B_defect Action Filter", markdown)
        self.assertIn("Unique B_defect selected: False", markdown)
        self.assertIn("J_defect selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
