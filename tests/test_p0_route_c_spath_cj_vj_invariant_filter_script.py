from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_cj_vj_invariant_filter import build_payload, render_markdown


class P0RouteCSPathCJVJInvariantFilterTests(unittest.TestCase):
    def test_filter_underselects_without_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-cj-vj-invariant-filter-underselects")
        self.assertTrue(payload["scalar_density_contract_written"])
        self.assertEqual(payload["admissible_invariant_count"], 5)
        self.assertEqual(payload["rejected_invariant_count"], 1)
        self.assertTrue(payload["all_survivors_underselect"])
        self.assertFalse(payload["source_coefficients_fixed"])
        self.assertFalse(payload["unique_cj_vj_selector_found"])
        self.assertFalse(payload["stability_signs_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_keep_covariant_families_and_reject_fit(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["invariant_rows"]}

        self.assertTrue(rows["curvature_difference_scalar"]["survives_filter"])
        self.assertTrue(rows["relative_metric_strain_trace"]["same_l_required"])
        self.assertTrue(rows["matter_cross_trace"]["same_l_required"])
        self.assertTrue(rows["holonomy_trace"]["survives_filter"])
        self.assertFalse(rows["observable_residual"]["survives_filter"])
        self.assertTrue(rows["observable_residual"]["uses_fit"])

    def test_criteria_forbid_manual_selection(self) -> None:
        payload = build_payload()
        criteria = " ".join(payload["filter_criteria"])

        self.assertIn("no observational residual", criteria)
        self.assertIn("same-L", criteria)
        self.assertIn("C_0>0", criteria)
        self.assertIn("Janus source provenance", criteria)
        self.assertIn("C_J=c0", payload["candidate_family"])

    def test_markdown_reports_underselection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("C_J/V_J Invariant Filter", markdown)
        self.assertIn("All survivors underselect: True", markdown)
        self.assertIn("Unique C_J/V_J selector found: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
