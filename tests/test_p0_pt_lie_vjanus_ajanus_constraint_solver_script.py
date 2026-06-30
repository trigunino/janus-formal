from __future__ import annotations

import unittest

from scripts.build_p0_pt_lie_vjanus_ajanus_constraint_solver import (
    build_payload,
    render_markdown,
)


class P0PtLieVjanusAjanusConstraintSolverTests(unittest.TestCase):
    def test_pt_lie_reduces_but_does_not_close(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "pt-lie-constraints-derived-branch-not-selected")
        self.assertFalse(payload["branch_selected_by_janus_source"])
        self.assertFalse(payload["coefficients_source_fixed"])
        self.assertFalse(payload["prediction_ready"])

    def test_vjanus_must_be_even_in_minimal_polynomial(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["v_even_residual"], "-2*c1*q - 2*c3*q**3")
        self.assertIn("c1", " ".join(payload["v_forbidden_coefficients"]))
        self.assertIn("c3", " ".join(payload["v_forbidden_coefficients"]))
        self.assertEqual(payload["v_allowed_shape"], "c0 + c2*q^2 + c4*q^4")
        self.assertEqual(payload["v_stability_condition_at_origin"], "2*c2 >= 0")

    def test_ajanus_has_two_parity_branches_not_selected(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["a_p_branch_residual"], "2*a0 + 2*a2*q**2")
        self.assertIn("a0", " ".join(payload["a_p_branch_forbidden_coefficients"]))
        self.assertIn("a2", " ".join(payload["a_p_branch_forbidden_coefficients"]))
        self.assertEqual(payload["a_pt_branch_residual"], "-2*a1*q - 2*a3*q**3")
        self.assertIn("a1", " ".join(payload["a_pt_branch_forbidden_coefficients"]))
        self.assertIn("a3", " ".join(payload["a_pt_branch_forbidden_coefficients"]))

    def test_conditional_dynamics_gate_selects_p_like_only_if_required(self) -> None:
        gate = build_payload()["conditional_dynamics_gate"]

        self.assertEqual(
            gate["selected_branch_if_linear_transport_required"],
            "P-like odd A_Janus",
        )
        self.assertTrue(gate["janus_source_requires_linear_transport"])
        self.assertEqual(gate["p_like_passes_if"], "a1 != 0")
        self.assertFalse(gate["pt_like_passes"])

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("PT/Lie V_Janus A_Janus", markdown)
        self.assertIn("allowed shape", markdown)
        self.assertIn("Conditional Dynamics Gate", markdown)
        self.assertIn("Remaining lock", markdown)
        self.assertIn("not by fit", markdown)


if __name__ == "__main__":
    unittest.main()
