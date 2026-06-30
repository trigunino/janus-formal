from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_relative_strain_action_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHRelativeStrainActionGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-relative-strain-action-gate-open",
        )
        self.assertFalse(payload["janus_tracefree_el_supplied"])
        self.assertFalse(payload["source_action_selects_tracefree_branch"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_tracefree_rank_and_selection_rule_are_explicit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["component_count"]["tracefree_h_rank"], 9)
        self.assertIn("H_TF/Q_TF", payload["candidate"])
        self.assertIn("Euler-Lagrange equation", payload["selection_rule"])
        self.assertIn("trace-free branch", payload["selection_rule"])

    def test_ultralocal_potential_is_algebraic_and_insufficient(self) -> None:
        ultralocal = build_payload()["ultralocal_vh"]

        self.assertEqual(ultralocal["action_class"], "ultralocal potential V(H)")
        self.assertEqual(ultralocal["el_equation_type"], "algebraic")
        self.assertFalse(ultralocal["sufficient_for_tracefree_branch"])
        self.assertIn("no D H or D Q provenance", ultralocal["reason"])

    def test_derivative_action_requirements_are_not_closed(self) -> None:
        derivative = build_payload()["derivative_action"]
        requirements = " ".join(derivative["requirements"])

        self.assertEqual(derivative["can_select_tracefree_branch"], "conditional")
        self.assertFalse(derivative["requirements_closed"])
        self.assertIn("source/action provenance", requirements)
        self.assertIn("boundary and gauge", requirements)
        self.assertIn("curl integrability", requirements)
        self.assertIn("mirror inverse", requirements)
        self.assertIn("same-L", requirements)
        self.assertIn("ghost/stability", requirements)

    def test_residual_target_and_trace_absorption_are_forbidden(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["residual_target_allowed"])
        self.assertFalse(payload["determinant_trace_absorption_allowed"])
        self.assertIn("residual target", forbidden)
        self.assertIn("determinant trace", forbidden)

    def test_markdown_reports_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Relative Strain Action", markdown)
        self.assertIn("Janus trace-free EL supplied: False", markdown)
        self.assertIn("Residual target allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
