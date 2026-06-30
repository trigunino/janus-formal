from __future__ import annotations

import unittest

from scripts.build_p0_scross_candidate_triage_matrix import build_payload, render_markdown


class P0ScrossCandidateTriageMatrixTests(unittest.TestCase):
    def test_search_space_is_reduced_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "search-space-reduced-physics-open")
        self.assertFalse(payload["free_choice_allowed"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["prediction_ready"])

    def test_rejects_pure_pullback_free_potential_and_wrong_sign(self) -> None:
        payload = build_payload()
        rejected = set(payload["rejected_families"])
        rows = {row["candidate"]: row for row in payload["rows"]}

        self.assertIn("pure_pullback_top_form", rejected)
        self.assertEqual(rows["pure_pullback_top_form"]["euler_lagrange_q"], "0")
        self.assertIn("free_ultralocal_potential", rejected)
        self.assertIn("hand-selected", rows["free_ultralocal_potential"]["verdict"])
        self.assertIn("wrong_sign_derivative_solder", rejected)
        self.assertIn("fail", rows["wrong_sign_derivative_solder"]["ghost_gate"])

    def test_keeps_two_minimal_viable_non_rustine_families(self) -> None:
        payload = build_payload()
        viable = set(payload["minimal_viable_families"])
        rows = {row["candidate"]: row for row in payload["rows"]}

        self.assertEqual(viable, {"source_derivative_solder", "bf_source_constraint"})
        self.assertTrue(rows["source_derivative_solder"]["has_transport"])
        self.assertTrue(rows["source_derivative_solder"]["source_anchored"])
        self.assertIn("conditional pass", rows["source_derivative_solder"]["ghost_gate"])
        self.assertTrue(rows["bf_source_constraint"]["has_transport"])
        self.assertIn("euler_lagrange_lambda", rows["bf_source_constraint"])

    def test_pt_lie_constraints_are_attached(self) -> None:
        constraints = build_payload()["pt_lie_constraints"]

        self.assertEqual(constraints["v_allowed_shape"], "c0 + c2*q^2 + c4*q^4")
        self.assertIn("a1*q", constraints["a_p_branch_allowed_shape"])
        self.assertIn("a2*q^2", constraints["a_pt_branch_allowed_shape"])
        self.assertFalse(constraints["branch_selected_by_janus_source"])
        self.assertFalse(constraints["coefficients_source_fixed"])

    def test_conditional_ajanus_branch_gate_is_attached(self) -> None:
        gate = build_payload()["conditional_ajanus_branch_gate"]

        self.assertEqual(
            gate["selected_if_linear_transport_required"],
            "P-like odd A_Janus",
        )
        self.assertFalse(gate["pt_like_passes_linear_gate"])
        self.assertTrue(gate["janus_source_requires_linear_transport"])
        self.assertTrue(gate["weakfield_linear_matching_selects_p_like"])

    def test_required_next_proofs_bind_to_full_janus_closure(self) -> None:
        proofs = " ".join(build_payload()["required_next_proofs"])

        self.assertIn("V_Janus or A_Janus", proofs)
        self.assertIn("covariant phi/L/Omega", proofs)
        self.assertIn("R_plus=0", proofs)
        self.assertIn("R_minus=0", proofs)
        self.assertIn("same L", proofs)

    def test_markdown_reports_notable_improvement(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Notable Improvement", markdown)
        self.assertIn("PT/Lie Constraints", markdown)
        self.assertIn("Conditional A branch", markdown)
        self.assertIn("source_derivative_solder", markdown)
        self.assertIn("bf_source_constraint", markdown)
        self.assertIn("future work should not search arbitrary couplings", markdown)


if __name__ == "__main__":
    unittest.main()
