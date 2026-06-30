from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_route_c_small_loop_holonomy_numeric_probe import (
    ETA,
    boost_generator,
    build_payload,
    eta_lie_error,
    render_markdown,
)


class P0RouteCSmallLoopHolonomyNumericProbeTests(unittest.TestCase):
    def test_probe_accepts_source_curvature_but_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "small-loop-holonomy-numeric-probe-open")
        self.assertTrue(payload["weakfield_relative_curvature_rows_used"])
        self.assertTrue(payload["lorentz_algebra_candidate"])
        self.assertTrue(payload["constant_curvature_holonomy_first_order_closes"])
        self.assertTrue(payload["constant_curvature_segmentation_closes"])
        self.assertTrue(payload["noncommuting_path_order_changes_holonomy"])
        self.assertFalse(payload["path_rule_source_derived"])
        self.assertFalse(payload["l_uniquely_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_defected_phi_r_is_rejected(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["phi_r_free_insert_allowed"])
        self.assertTrue(payload["curl_defected_phi_r_rejected"])
        self.assertGreater(payload["defected_eta_lie_error"], 1e-10)

    def test_boost_generator_is_lorentz_algebra(self) -> None:
        generator = boost_generator("x")

        self.assertLess(eta_lie_error(generator), 1e-12)
        self.assertLess(np.max(np.abs(generator.T @ ETA + ETA @ generator)), 1e-12)

    def test_markdown_reports_open_path_rule(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Small-Loop Holonomy", markdown)
        self.assertIn("Path rule source derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
