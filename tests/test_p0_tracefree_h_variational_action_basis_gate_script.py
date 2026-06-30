from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_variational_action_basis_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHVariationalActionBasisGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-variational-action-basis-gate-open",
        )
        self.assertEqual(payload["target_channel"], "S_TF^Janus for H_TF/Q_TF")
        self.assertEqual(payload["action_variables"], ["H", "L", "phi", "matter"])
        self.assertFalse(payload["requirements_closed"])
        self.assertFalse(payload["any_term_accepted"])
        self.assertFalse(payload["target_residual_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_requested_candidate_terms_are_present_and_unaccepted(self) -> None:
        rows = {row["term"]: row for row in build_payload()["candidate_terms"]}

        self.assertEqual(len(rows), 8)
        self.assertIn("tr_qtf2", rows)
        self.assertIn("tr_qtf3", rows)
        self.assertIn("dqtf_kinetic", rows)
        self.assertIn("dhtf_kinetic", rows)
        self.assertIn("qtf_pi_tf", rows)
        self.assertIn("qtf_weyl", rows)
        self.assertIn("qtf_phi_sigma", rows)
        self.assertIn("bf_gl_constraints", rows)
        self.assertTrue(all(row["status"] == "conditional" for row in rows.values()))
        self.assertFalse(any(row["accepted"] for row in rows.values()))

    def test_action_densities_cover_ultralocal_derivative_linear_constraint_basis(self) -> None:
        densities = " ".join(row["action_density"] for row in build_payload()["candidate_terms"])

        self.assertIn("Tr(Q_TF^2)", densities)
        self.assertIn("Tr(Q_TF^3)", densities)
        self.assertIn("D Q_TF . D Q_TF", densities)
        self.assertIn("D H_TF . D H_TF", densities)
        self.assertIn("Q_TF^{ab} Pi_TF_ab", densities)
        self.assertIn("Q_TF^{ab} E_ab/Weyl", densities)
        self.assertIn("Q_TF^{ab} Phi_Sigma_ab", densities)
        self.assertIn("BF/GL", densities)

    def test_acceptance_rule_lists_janus_obligations(self) -> None:
        payload = build_payload()
        text = " ".join(payload["acceptance_obligations"]) + " " + payload["acceptance_rule"]

        self.assertIn("S_Janus", text)
        self.assertIn("H, L, phi, matter", text)
        self.assertIn("boundary and gauge", text)
        self.assertIn("same-L", text)
        self.assertIn("mirror", text)
        self.assertIn("stability", text)
        self.assertEqual(payload["accepted_terms"], [])

    def test_residual_target_and_determinant_trace_are_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["target_residual_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertIn("residual target", forbidden)
        self.assertIn("determinant trace", forbidden)
        self.assertIn("log det(H)", forbidden)
        self.assertIn("B4vol", forbidden)

    def test_markdown_reports_basis_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Variational Action Basis", markdown)
        self.assertIn("S_TF^Janus", markdown)
        self.assertIn("Tr(Q_TF^2)", markdown)
        self.assertIn("Q_TF^{ab} Pi_TF_ab", markdown)
        self.assertIn("BF/GL", markdown)
        self.assertIn("Target residual allowed: False", markdown)
        self.assertIn("Determinant trace allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
