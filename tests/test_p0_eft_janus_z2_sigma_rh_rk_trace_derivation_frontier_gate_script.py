from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_rh_rk_trace_derivation_frontier_gate import (
    build_payload,
    render_markdown,
)


class RhRkTraceDerivationFrontierGateTests(unittest.TestCase):
    def test_frontier_blocks_only_on_full_sigma_variation(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["frontier"]["trace_targets_derived"])
        self.assertFalse(payload["frontier"]["minimal_basis_can_derive_traces"])
        self.assertFalse(payload["frontier"]["alpha_radial_to_trace_conversion_ready"])
        self.assertFalse(payload["frontier"]["trace_to_tensor_emission_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "derive_alpha_h_alpha_K_radial_coefficients_from_full_sigma_variation",
        )

    def test_markdown_reports_route_order(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("R_h/R_K Trace Derivation Frontier", markdown)
        self.assertIn("derive_alpha_h_radial_coefficient_values", markdown)


if __name__ == "__main__":
    unittest.main()
