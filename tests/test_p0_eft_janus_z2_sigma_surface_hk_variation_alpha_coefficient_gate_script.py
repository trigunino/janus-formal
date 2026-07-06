from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_variation_alpha_coefficient_gate import (
    build_payload,
    render_markdown,
)


class SurfaceHKVariationAlphaCoefficientGateTests(unittest.TestCase):
    def test_template_identifies_alpha_coefficients(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["surface_HK_variation_template_ready"])
        self.assertTrue(payload["alpha_identification_ready"])
        self.assertEqual(payload["template"]["alpha_h_ab"], "-1/2 * T_surface^ab")
        self.assertEqual(payload["template"]["alpha_K_ab"], "D^ab")

    def test_polynomial_density_bending_moment_recorded_as_template_only(self) -> None:
        density = build_payload()["polynomial_density_example"]

        self.assertIn("a0 + a1*K", density["L_Sigma"])
        self.assertIn("2*a3*K_ab", density["D_ab"])
        self.assertEqual(
            density["coefficient_status"],
            "template_only_not_active_Janus_values",
        )

    def test_conventions_and_active_coefficients_remain_blockers(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["conventions_ready"])
        self.assertFalse(payload["active_Janus_coefficients_derived"])
        self.assertEqual(
            payload["primary_blocker"],
            "active_Janus_Sigma_density_coefficients",
        )

    def test_markdown_contains_alpha_and_dab_formula(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("alpha_h_ab", markdown)
        self.assertIn("alpha_K_ab", markdown)
        self.assertIn("D_ab", markdown)


if __name__ == "__main__":
    unittest.main()
