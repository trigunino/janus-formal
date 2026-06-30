from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_action_operator_requirements_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHActionOperatorRequirementsGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-action-operator-requirements-open",
        )
        self.assertFalse(payload["accepted_action_route_supplied"])
        self.assertTrue(payload["stf_el_operator_required"])
        self.assertFalse(payload["stf_el_operator_supplied"])
        self.assertFalse(payload["requirements_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_accepted_route_requires_projected_el_operator(self) -> None:
        payload = build_payload()

        self.assertIn("Euler-Lagrange operator", payload["accepted_route_rule"])
        self.assertIn("P_STF", payload["accepted_route_rule"])
        self.assertIn("H_TF/Q_TF", payload["accepted_route_rule"])

    def test_operator_requirements_cover_traceability_and_closure(self) -> None:
        requirements = " ".join(build_payload()["operator_requirements"])

        self.assertIn("source/action provenance", requirements)
        self.assertIn("principal symbol", requirements)
        self.assertIn("stability/ghost", requirements)
        self.assertIn("boundary and gauge", requirements)
        self.assertIn("curl/integrability", requirements)
        self.assertIn("mirror inverse", requirements)
        self.assertIn("same-L", requirements)

    def test_ultralocal_vh_is_insufficient(self) -> None:
        ultralocal = build_payload()["ultralocal_vh"]

        self.assertEqual(ultralocal["action_class"], "ultralocal algebraic V(H)")
        self.assertEqual(ultralocal["operator_type"], "algebraic")
        self.assertFalse(ultralocal["sufficient_for_h_tf_q_tf"])
        self.assertIn("no principal symbol", ultralocal["reason"])

    def test_derivative_dh_dq_action_is_conditional(self) -> None:
        derivative = build_payload()["derivative_action"]
        classes = " ".join(derivative["action_classes"])

        self.assertIn("D H", classes)
        self.assertIn("D Q", classes)
        self.assertEqual(derivative["acceptance"], "conditional")
        self.assertIn("all operator requirements", derivative["condition"])

    def test_target_residual_and_trace_absorption_are_forbidden(self) -> None:
        payload = build_payload()
        rejected = " ".join(payload["rejected_shortcuts"])

        self.assertFalse(payload["target_residual_operator_allowed"])
        self.assertFalse(payload["determinant_trace_absorption_allowed"])
        self.assertIn("target residual operator", rejected)
        self.assertIn("determinant trace", rejected)
        self.assertIn("ultralocal algebraic V(H)", rejected)

    def test_markdown_reports_requirements_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action Operator Requirements", markdown)
        self.assertIn("STF EL operator required: True", markdown)
        self.assertIn("Target residual operator allowed: False", markdown)
        self.assertIn("Determinant trace absorption allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
