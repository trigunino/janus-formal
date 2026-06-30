from __future__ import annotations

import unittest

from scripts.build_p0_ajanus_covariant_lift_obligation import (
    build_payload,
    render_markdown,
)


class P0AjanusCovariantLiftObligationTests(unittest.TestCase):
    def test_lift_obligation_is_written_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "covariant-lift-obligation-written-not-closed")
        self.assertFalse(payload["weakfield_promotion_done"])
        self.assertFalse(payload["coefficients_source_fixed"])
        self.assertFalse(payload["global_branch_selected_by_full_janus_source"])
        self.assertFalse(payload["prediction_ready"])
        self.assertEqual(payload["selected_covariant_q_object"], "relative_strain_tensor_Q")
        self.assertTrue(payload["selected_covariant_q_regular_branch_defined"])
        self.assertEqual(
            payload["selected_covariant_q_derivative_gate"],
            "p0_relative_strain_q_derivative_omega_gate",
        )

    def test_coefficients_are_algebraic_source_matches(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["covariant_source_series"], "q**3*r3 + q*r1")
        self.assertEqual(payload["p_like_transport_series"], "a1*q + a3*q**3")
        self.assertEqual(payload["unmatched_residual"], "-a1*q - a3*q**3 + q**3*r3 + q*r1")
        self.assertEqual(payload["match_conditions"]["linear"], "-a1 + r1=0 -> a1=r1")
        self.assertEqual(payload["match_conditions"]["cubic"], "-a3 + r3=0 -> a3=r3")

    def test_required_covariant_objects_include_same_omega_and_mirror(self) -> None:
        text = " ".join(build_payload()["covariant_objects_required"])

        self.assertIn("Q[phi,L]", text)
        self.assertIn("FrechetLog_H[D_alpha H]", text)
        self.assertIn("R_Janus", text)
        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", text)
        self.assertIn("relative curvature", text)
        self.assertIn("mirror inverse", text)

    def test_markdown_reports_no_fit_rule_and_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("A_Janus Covariant Lift", markdown)
        self.assertIn("a1=r1", markdown)
        self.assertIn("a3=r3", markdown)
        self.assertIn("relative_strain_tensor_Q", markdown)
        self.assertIn("Q=1/2 log(H)", markdown)
        self.assertIn("p0_relative_strain_q_derivative_omega_gate", markdown)
        self.assertIn("not data-fitted", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
