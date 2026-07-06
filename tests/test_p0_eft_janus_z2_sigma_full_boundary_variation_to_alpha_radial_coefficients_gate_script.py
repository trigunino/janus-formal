from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_full_boundary_variation_to_alpha_radial_coefficients_gate import (
    build_payload,
    render_markdown,
)


class FullBoundaryVariationToAlphaRadialCoefficientsGateTests(unittest.TestCase):
    def test_blocks_on_explicit_metric_extrinsic_values(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["symbolic_sigma_support_closed"])
        self.assertFalse(payload["component_level_residual_values_available"])
        self.assertFalse(payload["linear_K_residual_available_after_Cartan_GHY_partition"])
        self.assertEqual(
            payload["primary_blocker"],
            "explicit_full_sigma_boundary_variation_metric_extrinsic_residual_values",
        )

    def test_output_contract_declares_alpha_radial_fields(self) -> None:
        payload = build_payload()
        fields = payload["required_output_contract"]["fields"]

        self.assertIn("alpha_h_radial_coefficient_values", fields)
        self.assertIn("alpha_K_radial_coefficient_values", fields)
        self.assertIn("R_Sigma_values", fields)
        self.assertIn("sqrt_abs_h_values", fields)

    def test_markdown_reports_excluded_sources(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Excluded Sources", markdown)
        self.assertIn("Cartan_GHY_linear_K_trace", markdown)
        self.assertIn("Required Output Contract", markdown)


if __name__ == "__main__":
    unittest.main()
