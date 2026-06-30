from __future__ import annotations

import unittest

from scripts.build_p0_ajanus_branch_selector_dynamics_gate import (
    build_payload,
    render_markdown,
)


class P0AjanusBranchSelectorDynamicsGateTests(unittest.TestCase):
    def test_gate_is_conditional_not_source_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "conditional-p-like-selection-if-linear-transport-required",
        )
        self.assertEqual(payload["conditional_selected_branch"], "P-like odd A_Janus")
        self.assertTrue(payload["janus_source_requires_linear_transport"])
        self.assertFalse(payload["coefficients_source_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_linearization_eliminates_pt_like_if_required(self) -> None:
        payload = build_payload()
        linear = payload["linearization_at_interface"]
        gate = payload["nondegenerate_linear_transport_gate"]

        self.assertEqual(linear["p_like_dA_dq_at_0"], "a1")
        self.assertEqual(linear["pt_like_dA_dq_at_0"], "0")
        self.assertEqual(gate["p_like_passes_if"], "a1 != 0")
        self.assertFalse(gate["pt_like_passes"])

    def test_linear_residual_matching_is_attached(self) -> None:
        matching = build_payload()["linear_residual_matching_gate"]

        self.assertTrue(matching["weakfield_rows_are_linear"])
        self.assertEqual(matching["p_like_linear_match_condition"], "-a1 + r1=0 -> a1=r1")
        self.assertFalse(matching["pt_like_can_match_nonzero_linear_residual"])
        self.assertIn("weak-field/non-equal", matching["scope"])

    def test_fixed_interface_shapes_are_explicit(self) -> None:
        inputs = build_payload()["input_from_pt_lie_gate"]

        self.assertEqual(inputs["p_like_shape"], "a1*q + a3*q**3")
        self.assertEqual(inputs["pt_like_shape_after_fixed_interface"], "a2*q**2")
        self.assertEqual(inputs["fixed_interface_condition"], "A(0)=0")

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("A_Janus Branch Selector", markdown)
        self.assertIn("PT-like passes: False", markdown)
        self.assertIn("Linear Residual Matching", markdown)
        self.assertIn("Remaining lock", markdown)
        self.assertIn("fix a1/a3", markdown)


if __name__ == "__main__":
    unittest.main()
