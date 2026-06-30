from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_derivative_branch_stability_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHDerivativeBranchStabilityGateTests(unittest.TestCase):
    def test_gate_is_open_conditional_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-derivative-branch-stability-source-gate-open",
        )
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertFalse(payload["accepted_branch_supplied"])
        self.assertEqual(payload["stf_el_operator_supplied"], "formal/conditional only")
        self.assertFalse(payload["requirements_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivative_kinetic_branches_are_recorded_as_conditional(self) -> None:
        rows = {row["term"]: row for row in build_payload()["candidate_actions"]}

        self.assertEqual(len(rows), 2)
        self.assertEqual(rows["dqtf_kinetic"]["action_density"], "D Q_TF . D Q_TF")
        self.assertEqual(rows["dhtf_kinetic"]["action_density"], "D H_TF . D H_TF")
        self.assertIn("P_STF(D*D Q_TF)", rows["dqtf_kinetic"]["formal_stf_el_operator"])
        self.assertIn("P_STF(D*D H_TF)", rows["dhtf_kinetic"]["formal_stf_el_operator"])
        self.assertTrue(
            all(row["can_provide_stf_el_operator"] == "conditional" for row in rows.values())
        )
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertEqual(build_payload()["accepted_actions"], [])

    def test_required_gates_cover_source_and_branch_stability(self) -> None:
        payload = build_payload()
        required = " ".join(payload["required_gates"])

        self.assertTrue(payload["janus_provenance_required"])
        self.assertFalse(payload["janus_provenance_supplied"])
        self.assertTrue(payload["boundary_gauge_required"])
        self.assertTrue(payload["curl_integrability_required"])
        self.assertTrue(payload["same_l_required"])
        self.assertTrue(payload["mirror_inverse_required"])
        self.assertIn("Janus source/action provenance", required)
        self.assertIn("boundary and gauge", required)
        self.assertIn("curl integrability", required)
        self.assertIn("same-L", required)
        self.assertIn("mirror inverse", required)
        self.assertIn("principal-symbol sign", required)

    def test_sign_conditions_are_necessary_not_sufficient(self) -> None:
        payload = build_payload()
        screen = payload["principal_symbol_screen"]
        signs = " ".join(screen["generic_sign_conditions"])

        self.assertTrue(screen["required"])
        self.assertFalse(screen["closed"])
        self.assertIn("ghost", screen["ghost_screen"])
        self.assertIn("tachyon", screen["tachyon_screen"])
        self.assertIn("kinetic", signs)
        self.assertIn("mass/Hessian", signs)
        self.assertTrue(screen["sign_conditions_necessary_not_sufficient"])
        self.assertTrue(payload["generic_sign_conditions_necessary"])
        self.assertFalse(payload["generic_sign_conditions_sufficient"])

    def test_residual_operator_and_determinant_trace_are_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["residual_operator_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertIn("residual operator", forbidden)
        self.assertIn("determinant trace", forbidden)
        self.assertIn("log det(H)", forbidden)
        self.assertIn("B4vol", forbidden)

    def test_markdown_reports_gate_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Derivative Branch Stability/Source Gate", markdown)
        self.assertIn("D Q_TF . D Q_TF", markdown)
        self.assertIn("D H_TF . D H_TF", markdown)
        self.assertIn("Generic sign conditions sufficient: False", markdown)
        self.assertIn("Residual operator allowed: False", markdown)
        self.assertIn("Determinant trace allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
