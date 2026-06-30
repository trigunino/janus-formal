from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_weakfield_tetrad_pipeline_probe import (
    ETA,
    build_payload,
    build_toy_weakfield_fields,
    central_gradient,
    central_hessian,
    curvature_injection_rows,
    lorentz_like_boost,
    render_markdown,
)


class P0WeakfieldTetradPipelineProbeTests(unittest.TestCase):
    def test_payload_is_bounded_numeric_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "bounded-p0-weakfield-tetrad-pipeline-probe")
        self.assertEqual(payload["tooling"], ["numpy"])
        self.assertTrue(payload["bounded_numeric_artifact"])
        self.assertFalse(payload["uses_fit"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_posthoc_qcross"])
        self.assertFalse(payload["uses_qdet_absorption"])
        self.assertFalse(payload["uses_scalar_absorption"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_weakfield_connection_rows_feed_curvature_rows(self) -> None:
        _, delta_phi, delta_psi = build_toy_weakfield_fields()
        grad_phi = central_gradient(delta_phi)
        hessian_phi = central_hessian(delta_phi)
        rows, residual = curvature_injection_rows(delta_phi, delta_psi)
        by_name = {row["row"]: row for row in rows}

        self.assertAlmostEqual(grad_phi["x"], 0.08, places=12)
        self.assertAlmostEqual(hessian_phi[("x", "y")], 0.012, places=12)
        self.assertLess(residual, 1e-12)
        self.assertAlmostEqual(by_name["Delta_F_0x0y"]["value"], 0.012, places=12)
        self.assertAlmostEqual(by_name["Delta_F_0x0y"]["direct_hessian_value"], 0.012, places=12)

    def test_consistent_same_l_branch_closes_mirror_and_qcross(self) -> None:
        payload = build_payload()
        branch = payload["consistent_branch"]

        self.assertTrue(branch["transport_mirror_closes"])
        self.assertTrue(branch["same_l_qcross_gate_closes"])
        self.assertLess(branch["transport_mirror_max_abs_residual"], 1e-12)
        self.assertLess(branch["same_l_max_residual"], 1e-12)
        for row in payload["qcross_rows"]:
            self.assertAlmostEqual(row["geometric_qcross"], row["same_l_optical_qcross"], places=12)

    def test_independent_optical_l_branch_is_rejected(self) -> None:
        payload = build_payload()
        branch = payload["inconsistent_independent_optical_l_branch"]

        self.assertFalse(branch["optical_mirror_closes"])
        self.assertFalse(branch["independent_optical_l_gate_closes"])
        self.assertFalse(branch["shortcut_allowed"])
        self.assertGreater(branch["optical_mirror_max_abs_residual"], 1e-3)
        self.assertGreater(branch["independent_l_min_residual"], 1e-3)
        self.assertNotEqual(payload["transport_beta_from_rows"], payload["independent_optical_beta"])

    def test_l_transforms_are_lorentz_like_and_rows_are_null(self) -> None:
        payload = build_payload()
        transform = lorentz_like_boost(payload["transport_beta_from_rows"])

        self.assertLess(np.max(np.abs(transform.T @ ETA @ transform - ETA)), 1e-12)
        self.assertLess(payload["transport_l_metric_error"], 1e-12)
        self.assertLess(payload["independent_optical_l_metric_error"], 1e-12)
        for row in payload["qcross_rows"]:
            self.assertLess(abs(row["null_error"]), 1e-12)

    def test_markdown_reports_forbidden_shortcuts_and_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Uses fit: False", markdown)
        self.assertIn("Uses posthoc Q_cross: False", markdown)
        self.assertIn("Uses Qdet absorption: False", markdown)
        self.assertIn("Physics closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Independent optical-L Q_cross closes: False", markdown)


if __name__ == "__main__":
    unittest.main()
