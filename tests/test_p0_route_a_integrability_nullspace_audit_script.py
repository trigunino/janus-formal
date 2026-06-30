from __future__ import annotations

import unittest

from scripts.build_p0_route_a_integrability_nullspace_audit import build_payload, render_markdown


class P0RouteAIntegrabilityNullspaceAuditTests(unittest.TestCase):
    def test_integrability_is_filter_not_selector(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "integrability-necessary-filter-underselects")
        self.assertTrue(payload["necessary_gate"])
        self.assertTrue(payload["compatible_probe_passes"])
        self.assertTrue(payload["defected_probe_fails"])
        self.assertTrue(payload["nonzero_nullspace_without_source"])
        self.assertFalse(payload["unique_phi_j_l_selected"])
        self.assertFalse(payload["prediction_ready"])

    def test_equations_include_required_constraints(self) -> None:
        equations = " ".join(row["equation"] for row in build_payload()["equation_rows"])

        self.assertIn("J=dphi", equations)
        self.assertIn("partial_[a J^mu_b]=0", equations)
        self.assertIn("det(dphi)!=0", equations)
        self.assertIn("L^T eta L=eta", equations)
        self.assertIn("B4vol", equations)
        self.assertIn("Q_cross", equations)

    def test_no_scouple_fit_or_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["requires_scouple"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])

    def test_markdown_reports_nullspace(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Integrability Nullspace", markdown)
        self.assertIn("Nonzero nullspace without source: True", markdown)
        self.assertIn("Unique phi/J/L selected: False", markdown)


if __name__ == "__main__":
    unittest.main()
