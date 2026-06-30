from __future__ import annotations

import unittest

from scripts.build_p0_relative_strain_q_derivative_omega_gate import (
    build_payload,
    render_markdown,
)


class P0RelativeStrainQDerivativeOmegaGateTests(unittest.TestCase):
    def test_dq_gate_is_open_and_not_prediction_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "dq-frechet-derivative-gate-open")
        self.assertFalse(payload["full_omega_alpha_selected"])
        self.assertFalse(payload["dq_closed"])
        self.assertFalse(payload["commuting_shortcut_allowed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(payload["dh_identity_closed"])
        self.assertFalse(payload["strain_generator_source_selected"])
        self.assertEqual(payload["dh_source_gate"], "p0_relative_strain_dh_lgeom_vs_lorentz_gate")

    def test_matrix_log_frechet_derivative_is_required(self) -> None:
        payload = build_payload()

        self.assertIn("FrechetLog_H[D_alpha H]", payload["matrix_log_derivative"])
        self.assertIn("integral_0^infty", payload["matrix_log_derivative"])
        self.assertIn("Gamma_alpha^dagger_eta + Gamma_alpha", payload["dh_source_identity"])
        self.assertEqual(payload["scalar_commuting_check"]["D Q"], "dh/(2*h)")
        self.assertIn("[H,D_alpha H]=0", payload["scalar_commuting_check"]["valid_only_if"])

    def test_naive_offdiag_derivative_is_rejected_generically(self) -> None:
        check = build_payload()["eigenbasis_offdiag_check"]

        self.assertIn("log(lambda_i)", check["frechet_offdiag"])
        self.assertIn("dH_ij", check["frechet_offdiag"])
        self.assertIn("dH_ij/(2*lambda_i)", check["naive_offdiag"])
        self.assertFalse(check["naive_equals_frechet_generically"])

    def test_same_omega_requirements_block_independent_q_connection(self) -> None:
        requirements = " ".join(build_payload()["same_omega_requirements"])

        self.assertIn("same L/Omega", requirements)
        self.assertIn("D_alpha H=0", requirements)
        self.assertIn("Q_cross", requirements)
        self.assertIn("Vlasov", requirements)
        self.assertIn("independent Q-connection", requirements)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Relative Strain Q Derivative", markdown)
        self.assertIn("Frechet", markdown)
        self.assertIn("H^{-1}DH shortcut", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
