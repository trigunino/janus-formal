from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_janus_metric_pullback_compatibility_gate import (
    ETA2,
    build_payload,
    coframe_from_metric_scales,
    frame_from_metric_scales,
    lorentz_residual_from_l,
    lorentz_residual_from_metric_residual,
    metric_pullback_residual,
    render_markdown,
    solder_l,
)


class P0JanusMetricPullbackCompatibilityGateTests(unittest.TestCase):
    def test_metric_pullback_lorentz_iff_is_derived_but_source_open(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "metric-pullback-compatibility-derived-source-selection-open",
        )
        self.assertTrue(payload["residual_identity_proved_numeric"])
        self.assertTrue(payload["metric_pullback_iff_lorentz"])
        self.assertTrue(payload["compatible_case_closes"])
        self.assertTrue(payload["mismatch_case_rejected"])
        self.assertFalse(payload["janus_source_selects_metric_pullback"])
        self.assertEqual(
            payload["phi_selector_artifact"],
            "p0_janus_metric_pullback_phi_selector_gate",
        )
        self.assertTrue(payload["phi_selector_equation_derived"])
        self.assertTrue(payload["pure_soldered_l_conditionally_admissible"])
        self.assertFalse(payload["pure_soldered_l_generally_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_residual_identity_matches_direct_lorentz_residual(self) -> None:
        jac = np.diag([1.2, 0.8])
        metric_other = ETA2.copy()
        metric_self = jac.T @ metric_other @ jac
        coframe_self = coframe_from_metric_scales(1.44, 0.64)
        frame_other = frame_from_metric_scales(1.0, 1.0)

        l_solder = solder_l(jac, coframe_self, frame_other)
        metric_residual = metric_pullback_residual(jac, metric_self, metric_other)
        direct = lorentz_residual_from_l(l_solder)
        identity = lorentz_residual_from_metric_residual(jac, frame_other, metric_residual)

        np.testing.assert_allclose(direct, identity, atol=1e-12)
        np.testing.assert_allclose(direct, np.zeros((2, 2)), atol=1e-12)

    def test_mismatch_cannot_be_hidden_by_qdet_or_qcross(self) -> None:
        payload = build_payload()
        mismatch = payload["mismatch_case"]

        self.assertGreater(mismatch["metric_pullback_residual_max"], 1e-4)
        self.assertGreater(mismatch["direct_lorentz_residual_max"], 1e-4)
        self.assertLess(mismatch["identity_error_max"], 1e-12)
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["requires_observational_fit"])

    def test_theorem_rows_include_janus_selection_gate(self) -> None:
        rows = {row["name"]: row for row in build_payload()["theorem_rows"]}

        self.assertIn("theta_s J_{s->o}^{-1} e_o", rows["soldered_l"]["formula"])
        self.assertIn("L^T eta L-eta", rows["residual_identity"]["formula"])
        self.assertIn("iff g_s=J^T g_o J", rows["iff_condition"]["formula"])
        self.assertFalse(rows["janus_selection_gate"]["closed"])

    def test_markdown_reports_conditional_not_predictive_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Metric Pullback Compatibility", markdown)
        self.assertIn("Residual identity proved numeric: True", markdown)
        self.assertIn("Phi selector equation derived: True", markdown)
        self.assertIn("Pure soldered-L generally closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
