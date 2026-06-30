from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_bf_gl_phi_sigma_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHBfGlPhiSigmaGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-bf-gl-phi-sigma-gate-open")
        self.assertFalse(payload["janus_phi_sigma_source_equation_supplied"])
        self.assertFalse(payload["janus_n_alpha_source_equation_supplied"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_phi_sigma_and_n_alpha_require_janus_source_equations(self) -> None:
        rows = {row["name"]: row for row in build_payload()["candidate_sources"]}

        self.assertIn("Phi_Sigma", rows)
        self.assertIn("N_alpha", rows)
        self.assertFalse(any(row["janus_equation_supplied"] for row in rows.values()))
        self.assertFalse(any(row["selects_h_tf_q_tf"] for row in rows.values()))
        self.assertIn("Janus action", rows["Phi_Sigma"]["blocker"])
        self.assertIn("Euler-Lagrange equation", rows["N_alpha"]["blocker"])

    def test_pure_bf_and_fitted_residual_routes_are_rejected(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rejected_routes"]}

        self.assertFalse(payload["pure_bf_selects_local_h_tf_dynamics"])
        self.assertFalse(payload["fitted_phi_sigma_allowed"])
        self.assertFalse(payload["residual_cancellation_allowed"])
        self.assertIn("pure_bf_topological_constraint", rows)
        self.assertIn("fitted_phi_sigma", rows)
        self.assertIn("residual_cancellation", rows)
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("do not select local H_TF dynamics", rows["pure_bf_topological_constraint"]["reason"])
        self.assertIn("not a Janus source equation", rows["fitted_phi_sigma"]["reason"])

    def test_required_integrability_transport_and_stability_checks_are_named(self) -> None:
        gate = {row["check"]: row for row in build_payload()["acceptance_gate"]}

        self.assertFalse(any(row["passed"] for row in gate.values()))
        self.assertIn("bianchi_curvature_integrability", gate)
        self.assertIn("gauge_fixing", gate)
        self.assertIn("mirror_inverse", gate)
        self.assertIn("same_l_transport", gate)
        self.assertIn("ghost_stability_if_propagating", gate)
        self.assertIn("Bianchi residuals", gate["bianchi_curvature_integrability"]["requirement"])
        self.assertIn("same L", gate["same_l_transport"]["requirement"])
        self.assertIn("ghost/tachyon stability", gate["ghost_stability_if_propagating"]["requirement"])

    def test_markdown_reports_prediction_false_and_guardrails(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("BF/GL Phi_Sigma Gate", markdown)
        self.assertIn("Pure BF selects local H_TF dynamics: False", markdown)
        self.assertIn("Fitted Phi_Sigma allowed: False", markdown)
        self.assertIn("Residual cancellation allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Bianchi/curvature integrability", markdown)


if __name__ == "__main__":
    unittest.main()
