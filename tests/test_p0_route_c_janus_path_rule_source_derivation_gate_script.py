from __future__ import annotations

import unittest

from scripts.build_p0_route_c_janus_path_rule_source_derivation_gate import (
    build_payload,
    render_markdown,
)


class P0RouteCJanusPathRuleSourceDerivationGateTests(unittest.TestCase):
    def test_no_zero_axiom_path_rule_is_selected(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-path-rule-source-derivation-gate-open")
        self.assertFalse(payload["zero_axiom_path_rule_selected"])
        self.assertFalse(payload["path_rule_source_derivation_closed"])
        self.assertTrue(payload["all_matrix_candidates_excluded"])
        self.assertTrue(payload["two_path_nonunique_l_blocks_prediction"])
        self.assertTrue(payload["janus_geodesics_available"])
        self.assertFalse(payload["janus_cross_sector_path_selector_available"])
        self.assertTrue(payload["new_path_axiom_required_if_selected_now"])
        self.assertFalse(payload["prediction_ready"])

    def test_source_rows_cover_geodesic_mirror_flrw_and_action_origins(self) -> None:
        origins = {row["origin"] for row in build_payload()["source_rows"]}

        self.assertIn("positive_geodesic_equation", origins)
        self.assertIn("negative_geodesic_equation", origins)
        self.assertIn("mirror_symmetry", origins)
        self.assertIn("pt_geometry", origins)
        self.assertIn("flrw_background", origins)
        self.assertIn("noether_action", origins)

    def test_markdown_reports_path_axiom_risk(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Path-Rule Source Derivation", markdown)
        self.assertIn("New path axiom required if selected now: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
