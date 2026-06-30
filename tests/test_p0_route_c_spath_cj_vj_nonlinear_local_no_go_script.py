from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_cj_vj_nonlinear_local_no_go import (
    build_payload,
    render_markdown,
)


class P0RouteCSPathCJVJNonlinearLocalNoGoTests(unittest.TestCase):
    def test_nonlinear_local_filter_only_no_go_is_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-cj-vj-nonlinear-local-no-go-closed")
        self.assertTrue(payload["nonlinear_local_family_considered"])
        self.assertTrue(payload["arbitrary_functions_survive"])
        self.assertFalse(payload["filters_generate_functional_equation"])
        self.assertFalse(payload["pt_samel_stability_select_unique_function"])
        self.assertTrue(payload["bounded_no_go_closed_for_local_filter_only_family"])
        self.assertTrue(payload["requires_source_equation_for_selection"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_are_filters_not_functional_equations(self) -> None:
        rows = {row["constraint"]: row for row in build_payload()["rows"]}

        self.assertEqual(
            set(rows),
            {
                "diagonal_scalar_covariance",
                "PT_mirror_parity",
                "same_l_compatibility",
                "stability_C0_V2",
                "weak_field_sign",
                "missing_source_EL",
            },
        )
        self.assertTrue(all(not row["equation_on_function"] for row in rows.values()))
        self.assertIn("higher jets", rows["weak_field_sign"]["effect"])
        self.assertIn("local sign", rows["stability_C0_V2"]["effect"])

    def test_explicit_survivor_family_keeps_free_functions(self) -> None:
        survivor = build_payload()["explicit_survivor_family"]

        self.assertIn("epsilon G_even", survivor["base"])
        self.assertIn("epsilon H_even", survivor["potential"])
        self.assertEqual(survivor["free_functions"], ["G_even", "H_even"])

    def test_markdown_reports_no_unique_function(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonlinear Local No-Go", markdown)
        self.assertIn("Arbitrary functions survive: True", markdown)
        self.assertIn("Filters generate functional equation: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
