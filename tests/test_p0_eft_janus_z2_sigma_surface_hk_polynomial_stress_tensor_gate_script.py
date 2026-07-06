from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_polynomial_stress_tensor_gate import (
    build_payload,
    render_markdown,
)


class SurfaceHKPolynomialStressTensorGateTests(unittest.TestCase):
    def test_alpha_h_and_alpha_k_formulas_are_derived(self) -> None:
        payload = build_payload()
        alpha = payload["alpha_coefficients"]

        self.assertTrue(payload["alpha_h_formula_ready"])
        self.assertTrue(payload["alpha_K_formula_ready"])
        self.assertIn("1/2*h^ab*L_Sigma", alpha["alpha_h_ab"])
        self.assertIn("(a1 + 2*a2*K)*K^ab", alpha["alpha_h_ab"])
        self.assertIn("2*a3*K^a_c*K^bc", alpha["alpha_h_ab"])
        self.assertEqual(alpha["alpha_K_ab"], "a1*h^ab + 2*a2*K*h^ab + 2*a3*K^ab")

    def test_radial_contraction_is_generic_and_active_values_remain_blocked(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["radial_contraction_formula_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["active_Janus_coefficients_ready"])
        self.assertFalse(payload["active_embedding_radial_derivatives_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "active_a_i_coefficients_and_radial_embedding_derivatives",
        )

    def test_markdown_reports_derivation(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Alpha Coefficients", markdown)
        self.assertIn("delta_h_inverse", markdown)
        self.assertIn("alpha_R", markdown)


if __name__ == "__main__":
    unittest.main()
