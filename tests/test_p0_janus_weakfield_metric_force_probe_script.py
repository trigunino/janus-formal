from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_metric_force_probe import build_payload, render_markdown


class P0JanusWeakfieldMetricForceProbeScriptTests(unittest.TestCase):
    def test_probe_reconstructs_metric_and_force(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["metric_reconstructed_from_tetrad"])
        self.assertTrue(payload["force_matches_negative_gradient_linear_branch"])
        self.assertTrue(payload["b4vol_1p1_computed"])
        self.assertLess(payload["metrics"]["max_abs_phi_error"], 1e-12)

    def test_probe_is_not_source_selected(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["source_selected_janus_metric"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source-selected Janus metric: False", markdown)
        self.assertIn("does not select the Janus metric/tetrad branch", markdown)


if __name__ == "__main__":
    unittest.main()
