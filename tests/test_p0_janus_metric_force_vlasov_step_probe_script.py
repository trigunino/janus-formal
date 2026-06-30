from __future__ import annotations

import unittest

from scripts.build_p0_janus_metric_force_vlasov_step_probe import build_payload, render_markdown


class P0JanusMetricForceVlasovStepProbeScriptTests(unittest.TestCase):
    def test_metric_force_step_is_stable_diagnostic(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["uses_metric_geodesic_force"])
        self.assertLess(payload["metrics"]["mass_error"], 1e-12)
        self.assertGreaterEqual(payload["metrics"]["min_f_final"], 0.0)
        self.assertGreater(payload["metrics"]["max_abs_acceleration"], 0.0)

    def test_not_source_selected_or_predictive(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_source_selected_janus_metric"])
        self.assertFalse(payload["uses_same_l_transport"])
        self.assertTrue(payload["diagnostic_only"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Uses metric geodesic force: True", markdown)
        self.assertIn("not a source-selected Janus phase-space transport law", markdown)


if __name__ == "__main__":
    unittest.main()
