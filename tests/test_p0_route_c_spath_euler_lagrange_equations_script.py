from __future__ import annotations

import unittest

from scripts.build_p0_route_c_spath_euler_lagrange_equations import (
    build_payload,
    render_markdown,
)


class P0RouteCSpathEulerLagrangeEquationsTests(unittest.TestCase):
    def test_formal_euler_lagrange_equations_are_derived_but_not_closed(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "spath-euler-lagrange-equations-formal-open")
        self.assertTrue(payload["gamma_el_derived_formally"])
        self.assertTrue(payload["l_transport_el_derived_formally"])
        self.assertTrue(payload["endpoint_boundary_terms_identified"])
        self.assertFalse(payload["lorentz_constraint_variation_closed"])
        self.assertFalse(payload["same_l_stack_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_variation_rows_cover_gamma_l_boundary_and_lorentz_constraint(self) -> None:
        rows = {row["variation"]: row for row in build_payload()["variation_rows"]}

        self.assertEqual(
            set(rows),
            {
                "delta_gamma S_path",
                "delta_L S_path",
                "endpoint_boundary_terms",
                "lorentz_constraint",
            },
        )
        self.assertTrue(rows["delta_gamma S_path"]["derived_formally"])
        self.assertTrue(rows["delta_L S_path"]["derived_formally"])
        self.assertFalse(rows["lorentz_constraint"]["derived_formally"])
        self.assertTrue(all(not row["closed_for_prediction"] for row in rows.values()))

    def test_representative_equations_contain_expected_terms(self) -> None:
        payload = build_payload()

        self.assertIn("C_J", payload["gamma_euler_lagrange_representative"])
        self.assertIn("V_J", payload["gamma_euler_lagrange_representative"])
        self.assertIn("omega", payload["transport_residual_representative"])
        self.assertIn("ell", payload["l_euler_lagrange_representative"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("S_path Euler-Lagrange", markdown)
        self.assertIn("Gamma EL derived formally: True", markdown)
        self.assertIn("Lorentz constraint variation closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
