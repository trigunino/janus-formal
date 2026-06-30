from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_weyl_shear_source_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHWeylShearSourceGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-weyl-shear-source-gate-open")
        self.assertTrue(payload["trace_free_diagnostics_present"])
        self.assertTrue(payload["projection_orientation_constraints"])
        self.assertFalse(payload["janus_source_field_equation_present"])
        self.assertFalse(payload["gauge_boundary_branch_fixed"])
        self.assertFalse(payload["full_h_tf_q_tf_selected"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_weyl_shear_and_screen_diagnostics_are_trace_free_only(self) -> None:
        rows = {row["name"]: row for row in build_payload()["diagnostics"]}

        self.assertIn("electric_weyl_E_mu_nu", rows)
        self.assertIn("congruence_shear_sigma_mu_nu", rows)
        self.assertIn("optical_screen_shear", rows)
        self.assertTrue(all(row["trace_free"] for row in rows.values()))
        self.assertFalse(any(row["selects_full_h_tf_q_tf"] for row in rows.values()))
        self.assertEqual(rows["optical_screen_shear"]["projected_dimension"], 2)

    def test_source_gauge_boundary_and_4d_law_are_required(self) -> None:
        payload = build_payload()
        blockers = " ".join(row["blocker"] for row in payload["diagnostics"])
        guardrails = " ".join(payload["guardrails"])

        self.assertIn("Janus source/field equation", blockers)
        self.assertIn("gauge and boundary branch", blockers)
        self.assertIn("not a 4D Janus source law", blockers)
        self.assertIn("2D screen lensing", guardrails)
        self.assertIn("4D source law", guardrails)

    def test_residual_fit_and_trace_free_identity_routes_are_rejected(self) -> None:
        rows = {row["route"]: row for row in build_payload()["rejected_routes"]}

        self.assertFalse(build_payload()["residual_fit_used"])
        self.assertIn("trace_free_identity_as_source", rows)
        self.assertIn("screen_lensing_inversion_to_4d_source", rows)
        self.assertIn("residual_fit", rows)
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("not a Janus source/field equation", rows["residual_fit"]["reason"])

    def test_markdown_reports_non_selection_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Weyl Shear Source Gate", markdown)
        self.assertIn("electric_weyl_E_mu_nu", markdown)
        self.assertIn("optical_screen_shear", markdown)
        self.assertIn("Full H_TF/Q_TF selected: False", markdown)
        self.assertIn("Residual fit used: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
