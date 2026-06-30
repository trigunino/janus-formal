from __future__ import annotations

import unittest

from scripts.build_p0_route_c_phi_r_relative_curvature_selector_probe import (
    build_payload,
    render_markdown,
)


class P0RouteCPhiRRelativeCurvatureSelectorProbeTests(unittest.TestCase):
    def test_probe_uses_source_curvature_without_free_phi_r(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phi-r-relative-curvature-selector-probe-open")
        self.assertEqual(payload["phi_r_source_candidate"], "weakfield_relative_curvature_rows")
        self.assertFalse(payload["phi_r_free_insert_allowed"])
        self.assertTrue(payload["curl_defected_phi_r_rejected"])
        self.assertTrue(payload["independent_optical_l_rejected"])
        self.assertTrue(payload["qdet_qcross_absorption_rejected"])
        self.assertTrue(payload["small_loop_holonomy_numeric_probe_available"])
        self.assertTrue(payload["small_loop_constant_curvature_closes"])
        self.assertTrue(payload["small_loop_segmentation_closes"])
        self.assertTrue(payload["noncommuting_path_order_changes_holonomy"])
        self.assertTrue(payload["two_path_nonunique_l_probe_available"])
        self.assertTrue(payload["two_paths_select_different_l"])
        self.assertTrue(payload["path_rule_required_for_unique_l"])
        self.assertTrue(payload["l_selected_conditionally"])
        self.assertFalse(payload["l_uniquely_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_probe_rows_cover_curvature_holonomy_segmentation_and_same_l(self) -> None:
        probes = {row["probe"] for row in build_payload()["probe_rows"]}

        self.assertEqual(
            probes,
            {
                "phi_r_source_candidate",
                "curvature_match_residual",
                "small_loop_holonomy_residual",
                "segmentation_invariance",
                "same_l_k_qcross_residual",
            },
        )

    def test_markdown_reports_selector_probe(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Relative Curvature Selector Probe", markdown)
        self.assertIn("Phi_R free insert allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
