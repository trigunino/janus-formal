from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_variational_source_template_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHVariationalSourceTemplateGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-variational-source-template-gate-open",
        )
        self.assertFalse(payload["requirements_closed"])
        self.assertFalse(payload["target_residual_source_allowed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_target_equation_is_projected_variational_source(self) -> None:
        payload = build_payload()
        equations = " ".join(payload["target_source_equations"])

        self.assertIn("P_STF(delta S_Janus/delta H)=0", equations)
        self.assertIn("P_STF(E_H - S_TF)=0", equations)
        self.assertIn("varying S_Janus", payload["target_source_rule"])
        self.assertIn("P_STF", payload["target_source_rule"])

    def test_required_ingredients_are_explicit(self) -> None:
        payload = build_payload()
        ingredients = {row["ingredient"] for row in payload["required_ingredients"]}
        requirements = " ".join(row["requirement"] for row in payload["required_ingredients"])

        self.assertEqual(payload["action_variables"], ["H", "L", "phi", "matter"])
        self.assertIn("action variables", ingredients)
        self.assertIn("variation domain", ingredients)
        self.assertIn("boundary terms", ingredients)
        self.assertIn("gauge constraints", ingredients)
        self.assertIn("same-L", ingredients)
        self.assertIn("mirror inverse", ingredients)
        self.assertIn("ghost/stability", ingredients)
        self.assertIn("source traceability", ingredients)
        self.assertIn("S_Janus[H, L, phi, matter]", requirements)
        self.assertFalse(any(row["closed"] for row in payload["required_ingredients"]))

    def test_ultralocal_potential_is_insufficient_alone(self) -> None:
        ultralocal = build_payload()["ultralocal_potential"]

        self.assertEqual(ultralocal["action_class"], "ultralocal potential V(H)")
        self.assertFalse(ultralocal["sufficient_alone"])
        self.assertIn("no derivative operator", ultralocal["reason"])

    def test_derivative_action_is_conditional(self) -> None:
        derivative = build_payload()["derivative_action"]
        classes = " ".join(derivative["action_classes"])

        self.assertIn("D H", classes)
        self.assertIn("D Q_TF", classes)
        self.assertEqual(derivative["acceptance"], "conditional")
        self.assertIn("all required ingredients", derivative["condition"])

    def test_target_residual_source_is_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["target_residual_source_allowed"])
        self.assertIn("target residual source", forbidden)
        self.assertIn("ultralocal V(H) alone", forbidden)
        self.assertIn("non-same-L", forbidden)

    def test_markdown_reports_template_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Variational Source Template", markdown)
        self.assertIn("P_STF(delta S_Janus/delta H)=0", markdown)
        self.assertIn("P_STF(E_H - S_TF)=0", markdown)
        self.assertIn("Target residual source allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
