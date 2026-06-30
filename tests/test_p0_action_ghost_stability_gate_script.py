from __future__ import annotations

import unittest

from scripts.build_p0_action_ghost_stability_gate import build_payload, render_markdown


class P0ActionGhostStabilityGateTests(unittest.TestCase):
    def test_gate_is_ready_but_no_candidate_is_accepted(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "gate-ready-candidate-actions-missing")
        self.assertFalse(payload["accepted_action_supplied"])
        self.assertFalse(payload["janus_candidate_tested"])
        self.assertFalse(payload["prediction_ready"])

    def test_positive_definite_conditions_are_explicit(self) -> None:
        conditions = payload_conditions()

        self.assertIn("k_plus > 0", conditions)
        self.assertIn("k_minus > 0", conditions)
        self.assertIn("k_plus*k_minus - k_cross^2 > 0", conditions)
        self.assertIn("m_plus*m_minus - m_cross^2 >= 0", conditions)

    def test_symbolic_gate_reports_eigenvalue_conditions(self) -> None:
        gate = build_payload()["symbolic_quadratic_gate"]

        self.assertIn("all kinetic eigenvalues > 0", gate["ghost_free_symbolic_condition"])
        self.assertIn("all mass eigenvalues >= 0", gate["tachyon_free_symbolic_condition"])
        self.assertEqual(len(gate["kinetic_eigenvalues"]), 2)
        self.assertEqual(len(gate["mass_eigenvalues"]), 2)

    def test_markdown_blocks_acceptance_without_source_action(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action Ghost Stability Gate", markdown)
        self.assertIn("derive the candidate quadratic action", markdown)
        self.assertIn("unbounded instabilities", markdown)


def payload_conditions() -> str:
    payload = build_payload()
    values = []
    for rows in payload["determinant_conditions"].values():
        values.extend(rows)
    return " ".join(values)


if __name__ == "__main__":
    unittest.main()
