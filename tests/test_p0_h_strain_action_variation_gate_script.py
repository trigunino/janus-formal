from __future__ import annotations

import unittest

from scripts.build_p0_h_strain_action_variation_gate import build_payload, render_markdown


class P0HStrainActionVariationGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "h-strain-action-variation-gate-open")
        self.assertEqual(payload["ghost_symbolic_gate"], "p0_h_strain_ghost_symbolic_gate")
        self.assertFalse(payload["ultralocal_el_contains_derivative"])
        self.assertTrue(payload["derivative_el_contains_second_derivative"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_toy_variations_distinguish_potential_from_derivative_action(self) -> None:
        payload = build_payload()

        self.assertIn("c1", payload["ultralocal_euler_lagrange"])
        self.assertNotIn("Derivative(q(x), (x, 2))", payload["ultralocal_euler_lagrange"])
        self.assertIn("Derivative(q(x), (x, 2))", payload["derivative_euler_lagrange"])

    def test_classification_blocks_ultralocal_dh_claim(self) -> None:
        rows = {row["action_class"]: row for row in build_payload()["classification"]}

        self.assertFalse(rows["ultralocal_potential_V_H"]["can_select_dh_or_sigma"])
        self.assertEqual(rows["derivative_strain_kinetic_DH2"]["can_select_dh_or_sigma"], "conditional")
        self.assertEqual(rows["bf_multiplier_target_N"]["can_select_dh_or_sigma"], "conditional")

    def test_markdown_reports_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("H Strain Action Variation", markdown)
        self.assertIn("p0_h_strain_ghost_symbolic_gate", markdown)
        self.assertIn("Ultralocal EL contains derivative: False", markdown)
        self.assertIn("Derivative EL contains second derivative: True", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
