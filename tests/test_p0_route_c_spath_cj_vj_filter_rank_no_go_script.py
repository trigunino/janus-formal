from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_cj_vj_filter_rank_no_go import build_payload, render_markdown


class P0RouteCSPathCJVJFilterRankNoGoTests(unittest.TestCase):
    def test_filter_rank_no_go_is_closed_for_filter_only_family(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-cj-vj-filter-rank-no-go-closed")
        self.assertEqual(payload["coefficient_variable_count"], 11)
        self.assertEqual(payload["compatibility_matrix_shape"], [0, 11])
        self.assertEqual(payload["compatibility_matrix_rank"], 0)
        self.assertEqual(payload["compatibility_nullity"], 11)
        self.assertFalse(payload["filters_select_unique_coefficients"])
        self.assertTrue(payload["rank_no_go_closed_for_filter_only_family"])
        self.assertEqual(payload["source_equations_required_for_unique_selection"], 11)
        self.assertFalse(payload["prediction_ready"])

    def test_proof_rows_contribute_no_rank(self) -> None:
        rows = {row["input"]: row for row in build_payload()["proof_rows"]}

        self.assertEqual(
            set(rows),
            {
                "no_fit_filter",
                "PT_same_L_filters",
                "stability_sign_inequalities",
                "weak_field_sign_filter",
                "missing_source_action",
            },
        )
        self.assertTrue(all(row["rank_contribution"] == 0 for row in rows.values()))
        self.assertIn("inequalities", rows["stability_sign_inequalities"]["reason"])
        self.assertIn("source equation", rows["missing_source_action"]["reason"])

    def test_coefficients_are_named(self) -> None:
        variables = build_payload()["coefficient_variables"]

        self.assertEqual(variables[0], "c0")
        self.assertIn("c5", variables)
        self.assertIn("v5", variables)
        self.assertEqual(len(variables), 11)

    def test_markdown_reports_no_selector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Filter Rank No-Go", markdown)
        self.assertIn("Compatibility matrix rank: 0", markdown)
        self.assertIn("Compatibility nullity: 11", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
