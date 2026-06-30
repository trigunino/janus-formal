from __future__ import annotations

import unittest

from scripts.build_p0_route_d_derivative_curvature_nullspace_gate import (
    build_payload,
    render_markdown,
)


class P0RouteDDerivativeCurvatureNullspaceGateTests(unittest.TestCase):
    def test_nullspace_gate_excludes_source_free_subfamily_only(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "derivative-curvature-nullspace-gate-open")
        self.assertTrue(payload["homogeneous_source_free_subfamily_excluded"])
        self.assertTrue(payload["source_free_boundary_no_go_bounded_claim_closed"])
        self.assertTrue(payload["source_free_pde_excluded_as_no_axiom_selector"])
        self.assertTrue(payload["periodic_kernel_detected"])
        self.assertTrue(payload["dirichlet_invertible_but_boundary_unsourced"])
        self.assertFalse(payload["derivative_curvature_family_fully_excluded"])
        self.assertFalse(payload["principal_symbol_stability_sufficient"])
        self.assertTrue(payload["source_derived_stf_curvature_operator_open"])
        self.assertEqual(payload["excluded_family_count"], 6)
        self.assertEqual(payload["open_family_count"], 1)
        self.assertFalse(payload["full_no_go_proved"])
        self.assertFalse(payload["prediction_ready"])

    def test_selector_defect_names_kernel_source_boundary_and_same_l(self) -> None:
        defect = build_payload()["selector_defect_definition"]

        self.assertIn("kernel", defect)
        self.assertIn("boundary", defect)
        self.assertIn("missing_source_rhs", defect)
        self.assertIn("missing_same_l_split_noether", defect)

    def test_markdown_reports_nullspace_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nullspace Gate", markdown)
        self.assertIn("Derivative/curvature family fully excluded: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
