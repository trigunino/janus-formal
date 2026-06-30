from __future__ import annotations

import unittest

from scripts.build_p0_h_strain_ghost_symbolic_gate import build_payload, render_markdown


class P0HStrainGhostSymbolicGateTests(unittest.TestCase):
    def test_gate_references_parent_gates_and_stays_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "h-strain-ghost-symbolic-gate-open")
        self.assertIn("p0_h_strain_action_variation_gate", payload["depends_on"])
        self.assertIn("p0_action_ghost_stability_gate", payload["depends_on"])
        self.assertFalse(payload["source_derived_action_supplied"])
        self.assertTrue(payload["source_derived_action_missing"])
        self.assertFalse(payload["prediction_ready"])

    def test_boundedness_conditions_are_explicit(self) -> None:
        conditions = build_payload()["boundedness_conditions"]

        self.assertIn("k_t > 0", conditions)
        self.assertIn("k_x > 0", conditions)
        self.assertIn("m^2 >= 0", conditions)

    def test_symbolic_derivation_builds_positive_hamiltonian_terms(self) -> None:
        derivation = build_payload()["symbolic_derivation"]

        self.assertIn("k_t*Derivative(q(t, x), t)**2/2", derivation["hamiltonian_density"])
        self.assertIn("k_x*Derivative(q(t, x), x)**2/2", derivation["hamiltonian_density"])
        self.assertIn("m^2*q(t, x)**2/2", derivation["hamiltonian_density"])
        self.assertIn("k_t*Derivative(q(t, x), (t, 2))", derivation["euler_lagrange"])
        self.assertIn("- k_x*Derivative(q(t, x), (x, 2))", derivation["euler_lagrange"])

    def test_instability_flags_cover_wrong_signs_and_tachyon(self) -> None:
        flags = {row["flag"]: row["condition"] for row in build_payload()["instability_flags"]}

        self.assertEqual(flags["wrong_sign_kinetic"], "k_t <= 0")
        self.assertEqual(flags["wrong_sign_gradient"], "k_x <= 0")
        self.assertEqual(flags["tachyon"], "m^2 < 0")

    def test_markdown_reports_missing_source_action(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("H/Q_TF strain", markdown)
        self.assertIn("Source-derived action missing: True", markdown)
        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("wrong_sign_kinetic", markdown)


if __name__ == "__main__":
    unittest.main()
