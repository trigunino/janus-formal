from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_janus_metric_pullback_phi_selector_gate import (
    ETA2,
    boost_1p1,
    build_payload,
    metric_from_scales,
    metric_pullback_residual,
    render_markdown,
    solve_constant_diagonal_jacobian,
)


class P0JanusMetricPullbackPhiSelectorGateTests(unittest.TestCase):
    def test_selector_equation_is_derived_but_general_source_closure_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "metric-pullback-phi-selector-derived-conditional-no-general-source-closure",
        )
        self.assertTrue(payload["phi_selector_equation_derived"])
        self.assertTrue(payload["constant_metric_phi_selected"])
        self.assertTrue(payload["jacobian_integrability_required"])
        self.assertTrue(payload["curvature_matching_required"])
        self.assertTrue(payload["boundary_gauge_required_for_unique_phi"])
        self.assertFalse(payload["janus_source_selects_one_phi"])
        self.assertEqual(
            payload["source_isometry_audit_artifact"],
            "p0_janus_source_isometry_selection_no_go",
        )
        self.assertFalse(payload["janus_source_selects_generic_metric_isometry"])
        self.assertTrue(payload["pure_l_solder_generic_route_rejected"])
        self.assertFalse(payload["metric_pullback_selection_generally_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_constant_metric_solution_has_zero_residual(self) -> None:
        metric_self = metric_from_scales(1.44, 0.64)
        jacobian = solve_constant_diagonal_jacobian(metric_self, ETA2)
        residual = metric_pullback_residual(jacobian, metric_self, ETA2)

        np.testing.assert_allclose(jacobian, np.diag([1.2, 0.8]), atol=1e-12)
        np.testing.assert_allclose(residual, np.zeros((2, 2)), atol=1e-12)

    def test_lorentz_family_shows_underselection(self) -> None:
        payload = build_payload()
        metric_self = metric_from_scales(1.44, 0.64)
        base = solve_constant_diagonal_jacobian(metric_self, ETA2)
        boosted = boost_1p1(0.2) @ base
        residual = metric_pullback_residual(boosted, metric_self, ETA2)

        np.testing.assert_allclose(residual, np.zeros((2, 2)), atol=1e-12)
        self.assertTrue(payload["lorentz_killing_family_underselected"])
        self.assertTrue(payload["lorentz_family_case"]["shows_killing_lorentz_underselection"])

    def test_curvature_obstruction_blocks_non_isometric_branch(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["curvature_obstruction_detected"])
        self.assertGreater(
            payload["curvature_obstruction_case"]["curvature_mismatch_max_abs"],
            1e-3,
        )
        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])

    def test_markdown_reports_conditional_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Metric Pullback Phi Selector", markdown)
        self.assertIn("Constant metric phi selected: True", markdown)
        self.assertIn("Janus source selects one phi: False", markdown)
        self.assertIn("Pure L_solder generic route rejected: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
