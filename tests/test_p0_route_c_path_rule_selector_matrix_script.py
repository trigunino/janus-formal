from __future__ import annotations

import unittest

from scripts.build_p0_route_c_path_rule_selector_matrix import build_payload, render_markdown


class P0RouteCPathRuleSelectorMatrixTests(unittest.TestCase):
    def test_matrix_rejects_unsourced_path_rules_for_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "path-rule-selector-matrix-open")
        self.assertEqual(payload["candidate_rule_count"], 8)
        self.assertEqual(payload["accepted_rule_count"], 0)
        self.assertTrue(payload["all_candidates_excluded_for_prediction"])
        self.assertTrue(payload["structural_mirror_boundary_insufficient"])
        self.assertFalse(payload["strong_boundary_selector_source_supplied"])
        self.assertFalse(payload["prediction_ready"])

    def test_rules_include_geometric_and_boundary_candidates(self) -> None:
        rules = {row["rule"] for row in build_payload()["rows"]}

        self.assertIn("positive_null_ray", rules)
        self.assertIn("spin_connection_autoparallel", rules)
        self.assertIn("mirror_symmetric_biloop", rules)
        self.assertIn("flrw_background_normal", rules)

    def test_markdown_reports_acceptance_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Path-Rule Selector Matrix", markdown)
        self.assertIn("All candidates excluded for prediction: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
