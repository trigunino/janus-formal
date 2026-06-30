from __future__ import annotations

import unittest

from scripts.build_p0_phi_sigma_source_action_decision_gate import (
    build_payload,
    render_markdown,
)


class P0PhiSigmaSourceActionDecisionGateTests(unittest.TestCase):
    def test_decision_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phi-sigma-source-action-decision-open")
        self.assertFalse(payload["source_phi_sigma_found"])
        self.assertFalse(payload["action_phi_sigma_found"])
        self.assertFalse(payload["any_branch_accepted"])
        self.assertTrue(payload["new_axiom_risk"])
        self.assertFalse(payload["new_axiom_adopted"])
        self.assertFalse(payload["closure_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_branches_are_unaccepted(self) -> None:
        rows = {row["branch"]: row for row in build_payload()["decision_branches"]}

        self.assertFalse(rows["source_derived_phi_sigma_or_n_alpha"]["accepted"])
        self.assertFalse(rows["action_derived_phi_sigma_or_n_alpha"]["accepted"])
        self.assertFalse(rows["new_axiom"]["accepted"])
        self.assertIn("published/source-local", rows["source_derived_phi_sigma_or_n_alpha"]["requires"])
        self.assertIn("EL equation", rows["action_derived_phi_sigma_or_n_alpha"]["requires"])
        self.assertIn("not adopted", rows["new_axiom"]["current_blocker"])

    def test_dependency_statuses_are_carried(self) -> None:
        statuses = build_payload()["dependency_status"]

        self.assertEqual(
            statuses["p0_sigma_source_traceability_gap_gate"],
            "sigma-source-traceability-gap-open",
        )
        self.assertEqual(
            statuses["p0_relative_metric_nonmetricity_sigma_dh_gate"],
            "relative-metric-nonmetricity-selector-open",
        )
        self.assertEqual(
            statuses["p0_cartan_bf_gl_strain_selector_gate"],
            "cartan-bf-gl-strain-selector-open",
        )
        self.assertEqual(
            statuses["p0_h_strain_action_variation_gate"],
            "h-strain-action-variation-gate-open",
        )

    def test_guardrails_forbid_residual_cancel_targets_and_fit(self) -> None:
        payload = build_payload()
        text = " ".join(payload["guardrails"])

        self.assertFalse(payload["residual_cancellation_target_allowed"])
        self.assertFalse(payload["observational_fit_allowed"])
        self.assertIn("residual-cancel target", text)
        self.assertIn("do not fit Phi_Sigma/N_alpha", text)
        self.assertIn("N_alpha := D_alpha H", text)

    def test_markdown_reports_branch_state(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Phi Sigma Source Action Decision", markdown)
        self.assertIn("Any branch accepted: False", markdown)
        self.assertIn("New axiom risk: True", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
