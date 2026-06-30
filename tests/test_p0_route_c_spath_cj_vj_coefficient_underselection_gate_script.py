from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_cj_vj_coefficient_underselection_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCSPathCJVJCoefficientUnderselectionGateTests(unittest.TestCase):
    def test_coefficients_remain_underselected(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-cj-vj-coefficient-underselection-open")
        self.assertEqual(payload["admissible_invariant_count"], 5)
        self.assertEqual(payload["linear_family_free_coefficients_lower_bound"], 11)
        self.assertTrue(payload["compatibility_constraints_written"])
        self.assertFalse(payload["coefficient_selection_equations_available"])
        self.assertTrue(payload["all_constraints_are_filters_not_selectors"])
        self.assertFalse(payload["unique_coefficient_solution_found"])
        self.assertFalse(payload["prediction_ready"])

    def test_constraints_do_not_fix_coefficients(self) -> None:
        rows = {row["constraint"]: row for row in build_payload()["constraint_rows"]}

        self.assertEqual(
            set(rows),
            {
                "no_observational_fit",
                "PT_mirror_parity",
                "same_l_compatibility",
                "stability_signs",
                "weak_field_sign",
                "source_provenance",
            },
        )
        self.assertTrue(all(not row["fixes_coefficients"] for row in rows.values()))
        self.assertIn("C_0>0", rows["stability_signs"]["effect"])
        self.assertIn("Janus equations/action", rows["source_provenance"]["effect"])

    def test_markdown_reports_filter_not_selector(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Coefficient Underselection Gate", markdown)
        self.assertIn("All constraints are filters not selectors: True", markdown)
        self.assertIn("Unique coefficient solution found: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
