from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_defect_matching_law_gate import (
    build_payload,
    render_markdown,
)


class P0OrbifoldPTDefectMatchingLawGateTests(unittest.TestCase):
    def test_defect_matching_law_is_written_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-defect-matching-law-open")
        self.assertTrue(payload["sigma_pt_law_written"])
        self.assertTrue(payload["pt_identification_source_derived"])
        self.assertTrue(payload["flux_jump_condition_written"])
        self.assertTrue(payload["defect_action_required"])
        self.assertFalse(payload["defect_action_source_derived"])
        self.assertTrue(payload["j_defect_formula_written"])
        self.assertFalse(payload["j_defect_source_derived"])
        self.assertTrue(payload["a_pt_boundary_condition_written"])
        self.assertFalse(payload["a_pt_boundary_condition_closed"])
        self.assertFalse(payload["unique_defect_current_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_pt_flux_action_metric_and_boundary(self) -> None:
        rows = {row["condition"]: row for row in build_payload()["matching_rows"]}

        self.assertEqual(
            set(rows),
            {
                "pt_orbifold_identification",
                "flux_jump",
                "defect_action_variation",
                "metric_matching",
                "a_pt_boundary_condition",
            },
        )
        self.assertTrue(rows["pt_orbifold_identification"]["source_derived"])
        self.assertFalse(rows["flux_jump"]["selects_current"])
        self.assertIn("J_defect", rows["defect_action_variation"]["formula"])
        self.assertIn("Sigma_PT", rows["a_pt_boundary_condition"]["formula"])

    def test_markdown_reports_underselection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Defect Matching Law Gate", markdown)
        self.assertIn("J_defect source-derived: False", markdown)
        self.assertIn("A_PT boundary condition closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
