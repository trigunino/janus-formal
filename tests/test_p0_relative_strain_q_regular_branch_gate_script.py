from __future__ import annotations

import unittest

from scripts.build_p0_relative_strain_q_regular_branch_gate import (
    build_payload,
    render_markdown,
)


class P0RelativeStrainQRegularBranchGateTests(unittest.TestCase):
    def test_q_branch_is_defined_but_not_source_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "relative-strain-q-regular-branch-defined-not-source-closed",
        )
        self.assertTrue(payload["q_regular_branch_defined"])
        self.assertFalse(payload["q_source_selected"])
        self.assertFalse(payload["q_derivative_closed"])
        self.assertFalse(payload["same_l_omega_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_mirror_inverse_makes_q_odd(self) -> None:
        check = build_payload()["scalar_eigen_check"]

        self.assertEqual(check["q_eigen"], "log(h)/2")
        self.assertIn("log(1/h)", check["mirror_q_eigen"])
        self.assertEqual(check["mirror_odd_residual"], "0")

    def test_trace_is_only_determinant_part(self) -> None:
        payload = build_payload()

        self.assertIn("Tr(Q)=1/2 log det(H)", payload["trace_relation"])
        self.assertIn("trace-free", payload["anisotropic_part"])
        self.assertIn("non-volume solder strain", payload["anisotropic_part"])

    def test_regular_and_derivative_obligations_are_carried_forward(self) -> None:
        payload = build_payload()
        regularity = " ".join(payload["regularity_from_polar_gate"])
        derivative = " ".join(payload["derivative_obligations"])

        self.assertIn("invertible", regularity)
        self.assertIn("square-root branch", regularity)
        self.assertIn("H^{1/2}", derivative)
        self.assertIn("D_alpha H", derivative)
        self.assertEqual(payload["derivative_gate"], "p0_relative_strain_q_derivative_omega_gate")
        self.assertEqual(payload["dh_source_gate"], "p0_relative_strain_dh_lgeom_vs_lorentz_gate")
        self.assertIn("FrechetLog_H[D_alpha H]", payload["derivative_rule"])
        self.assertIn("[H,D_alpha H]=0", payload["derivative_rule"])

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Relative Strain Q", markdown)
        self.assertIn("Q=1/2 log(H)", markdown)
        self.assertIn("trace-free", markdown)
        self.assertIn("p0_relative_strain_q_derivative_omega_gate", markdown)
        self.assertIn("p0_relative_strain_dh_lgeom_vs_lorentz_gate", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
