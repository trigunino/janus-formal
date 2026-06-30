from __future__ import annotations

import unittest

from scripts.build_p0_janus_source_isometry_selection_no_go import (
    build_payload,
    render_markdown,
    weakfield_identity_isometry_residuals,
)


class P0JanusSourceIsometrySelectionNoGoTests(unittest.TestCase):
    def test_janus_source_does_not_select_generic_isometry(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-source-does-not-select-generic-metric-isometry")
        self.assertTrue(payload["identity_branch_requires_equal_phi"])
        self.assertTrue(payload["identity_branch_requires_equal_psi"])
        self.assertTrue(payload["curvature_matching_required"])
        self.assertTrue(payload["b4vol_selects_measure_not_isometry"])
        self.assertFalse(payload["janus_source_selects_generic_metric_isometry"])
        self.assertTrue(payload["special_equal_branch_conditionally_allowed"])
        self.assertTrue(payload["pure_l_solder_generic_route_rejected"])
        self.assertFalse(payload["prediction_ready"])

    def test_identity_residuals_force_equal_potentials(self) -> None:
        residuals = weakfield_identity_isometry_residuals()

        self.assertIn("Phi_plus", residuals["time"])
        self.assertIn("Phi_minus", residuals["time"])
        self.assertIn("Psi_plus", residuals["space"])
        self.assertIn("Psi_minus", residuals["space"])

    def test_audit_rows_keep_special_branch_separate_from_general_route(self) -> None:
        rows = {row["row"]: row for row in build_payload()["audit_rows"]}

        self.assertFalse(rows["identity_metric_pullback"]["source_derives_isometry"])
        self.assertFalse(rows["poisson_source_rows"]["source_derives_isometry"])
        self.assertFalse(rows["curvature_matching"]["source_derives_isometry"])
        self.assertTrue(rows["special_equal_branch"]["source_derives_isometry"])
        self.assertIn("relative residual", rows["poisson_source_rows"]["imposes"])

    def test_no_fit_or_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_no_go(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source Isometry Selection No-Go", markdown)
        self.assertIn("Janus source selects generic metric isometry: False", markdown)
        self.assertIn("Pure L_solder generic route rejected: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
