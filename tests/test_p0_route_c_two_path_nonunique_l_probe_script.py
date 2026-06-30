from __future__ import annotations

import unittest

from scripts.build_p0_route_c_two_path_nonunique_l_probe import build_payload, render_markdown


class P0RouteCTwoPathNonuniqueLProbeTests(unittest.TestCase):
    def test_two_path_probe_shows_underselection(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "two-path-nonunique-l-probe-open")
        self.assertTrue(payload["generator_x_lorentz_algebra"])
        self.assertTrue(payload["generator_y_lorentz_algebra"])
        self.assertTrue(payload["two_paths_both_admissible_locally"])
        self.assertTrue(payload["two_paths_select_different_l"])
        self.assertTrue(payload["path_rule_required_for_unique_l"])
        self.assertFalse(payload["janus_path_rule_supplied"])
        self.assertFalse(payload["prediction_ready"])

    def test_metric_errors_remain_small(self) -> None:
        payload = build_payload()

        self.assertLess(payload["path_xy_metric_error"], 1e-12)
        self.assertLess(payload["path_yx_metric_error"], 1e-12)
        self.assertGreater(payload["two_path_l_residual"], 1e-10)

    def test_markdown_reports_nonunique_l(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Two-Path Nonunique L", markdown)
        self.assertIn("Path rule required for unique L: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
