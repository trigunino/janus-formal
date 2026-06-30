from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_g0i_dust_beta_inversion_target import (
    beta_minus_to_plus_from_plus_g0i,
    beta_plus_to_minus_from_minus_g0i,
    build_payload,
    render_markdown,
)


class P0JanusG0iDustBetaInversionTargetTests(unittest.TestCase):
    def test_plus_receiver_beta_inversion_solves_transverse_row(self) -> None:
        lap_b, chi, rho_plus, beta_plus, b4, rho_minus_to_plus = sp.symbols(
            "LapB_plus_i chi rho_plus beta_plus_i B_4vol_plus_from_minus rho_minus_to_plus"
        )
        beta_minus = beta_minus_to_plus_from_plus_g0i()
        residual = sp.simplify(-lap_b / (2 * chi) - rho_plus * beta_plus - b4 * rho_minus_to_plus * beta_minus)

        self.assertEqual(residual, 0)

    def test_minus_receiver_beta_inversion_solves_transverse_row(self) -> None:
        lap_b, chi, rho_minus, beta_minus, b4, rho_plus_to_minus = sp.symbols(
            "LapB_minus_i chi rho_minus beta_minus_i B_4vol_minus_from_plus rho_plus_to_minus"
        )
        beta_plus = beta_plus_to_minus_from_minus_g0i()
        residual = sp.simplify(lap_b / (2 * chi) - rho_minus * beta_minus - b4 * rho_plus_to_minus * beta_plus)

        self.assertEqual(residual, 0)

    def test_payload_is_conditional_dust_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "g0i-dust-beta-inversion-target-open")
        self.assertTrue(payload["g0i_dust_inversion_written"])
        self.assertTrue(payload["conditional_dust_beta_available"])
        self.assertFalse(payload["perfect_fluid_beta_available"])
        self.assertFalse(payload["anisotropic_beta_available"])
        self.assertFalse(payload["prediction_ready"])

    def test_forbids_fit_and_pressure_pi_shortcut(self) -> None:
        forbidden = " ".join(build_payload()["not_allowed"])

        self.assertIn("p or Pi0i", forbidden)
        self.assertIn("fit beta_i", forbidden)
        self.assertIn("Q_cross", forbidden)

    def test_markdown_reports_conditional_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Conditional dust beta available: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
