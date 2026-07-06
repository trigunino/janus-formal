from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_surface_hk_normal_flow_geometry_formula_gate import (
    build_payload,
    render_markdown,
)


class SurfaceHKNormalFlowGeometryFormulaGateTests(unittest.TestCase):
    def test_normal_flow_formulas_are_ready_but_active_curvature_is_missing(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["normal_flow_formula_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(payload["formulas"]["partial_R_h_ab"], "2*K_ab")
        self.assertEqual(payload["formulas"]["partial_R_K_ab"], "R_nabn + K_a^c*K_cb")
        self.assertEqual(payload["primary_blocker"], "active_K_ab_and_R_nabn_projection")

    def test_markdown_reports_curvature_projection(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("R_nabn", markdown)
        self.assertIn("partial_R_K_ab", markdown)


if __name__ == "__main__":
    unittest.main()
