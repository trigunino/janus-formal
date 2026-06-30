from __future__ import annotations

import unittest

from scripts.build_p0_curvature_scouple_selector_obstruction import (
    build_payload,
    render_markdown,
)


class P0CurvatureScoupleSelectorObstructionTests(unittest.TestCase):
    def test_curvature_terms_produce_equations_but_not_unique_selector(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "curvature-scouple-selector-obstruction-open")
        self.assertTrue(payload["curvature_terms_produce_map_equations"])
        self.assertFalse(payload["curvature_terms_select_unique_phi_j_l"])
        self.assertTrue(all(row["produces_map_equation"] for row in payload["rows"]))
        self.assertTrue(all(not row["selects_unique_map"] for row in payload["rows"]))

    def test_symbolic_forms_expose_obstructions(self) -> None:
        payload = build_payload()

        self.assertIn("Derivative(R_plus(x), x)", payload["curvature_weighted_top_form_el"])
        self.assertIn("Derivative(phi(x), (x, 2))", payload["curvature_weighted_kinetic_el"])
        self.assertIn("Derivative(R_minus(phi(x)), phi(x))", payload["scalar_curvature_match_el"])
        self.assertTrue(payload["scalar_curvature_matching_degenerate"])

    def test_source_obligations_remain(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["requires_source_derived_curvature_branch"])
        self.assertTrue(payload["requires_source_derived_coefficients"])
        self.assertTrue(payload["requires_boundary_or_initial_data"])
        self.assertTrue(payload["requires_same_l_tensor_residual_proof"])
        self.assertTrue(payload["requires_split_noether_proof"])
        self.assertTrue(payload["new_axiom_if_adopted_without_source"])

    def test_zero_rustine_guards_and_markdown(self) -> None:
        payload = build_payload()
        markdown = render_markdown(payload)

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["hidden_axiom_used"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])
        self.assertIn("Curvature terms select unique phi/J/L: False", markdown)
        self.assertIn("Scalar curvature matching degenerate: True", markdown)


if __name__ == "__main__":
    unittest.main()
