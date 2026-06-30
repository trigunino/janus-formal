from __future__ import annotations

import unittest

from scripts.build_p0_orbifold_pt_topological_defect_branch_gate import (
    build_payload,
    render_markdown,
)


class P0OrbifoldPTTopologicalDefectBranchGateTests(unittest.TestCase):
    def test_topological_branch_is_best_but_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "orbifold-pt-topological-defect-branch-open")
        self.assertTrue(payload["topological_branch_is_best_current_candidate"])
        self.assertTrue(payload["geometric_current_written"])
        self.assertFalse(payload["uses_matter_moments"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["coefficient_k_top_source_derived"])
        self.assertFalse(payload["dimension_degree_fixed"])
        self.assertFalse(payload["split_noether_bianchi_proved"])
        self.assertFalse(payload["stability_closed"])
        self.assertFalse(payload["branch_accepted"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidate_action_and_current_are_written(self) -> None:
        payload = build_payload()

        self.assertIn("Transgression", payload["candidate_action"])
        self.assertIn("tau^*A_PT", payload["candidate_action"])
        self.assertIn("delta B_top", payload["candidate_current"])

    def test_rows_cover_open_obligations(self) -> None:
        rows = {row["test"]: row for row in build_payload()["rows"]}

        self.assertEqual(
            set(rows),
            {
                "pt_mirror_covariance",
                "a_pt_boundary_current",
                "coefficient_selection",
                "dimensional_match",
                "split_noether",
                "stability",
            },
        )
        self.assertEqual(rows["coefficient_selection"]["result"], "fail-open")
        self.assertEqual(rows["a_pt_boundary_current"]["result"], "formal-pass")

    def test_markdown_reports_open_branch(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Topological Defect Branch", markdown)
        self.assertIn("Geometric current written: True", markdown)
        self.assertIn("Coefficient k_top source-derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
