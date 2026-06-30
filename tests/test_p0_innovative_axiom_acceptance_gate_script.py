from __future__ import annotations

import unittest

from scripts.build_p0_innovative_axiom_acceptance_gate import build_payload, render_markdown


class P0InnovativeAxiomAcceptanceGateTests(unittest.TestCase):
    def test_gate_allows_research_but_not_prediction(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "innovative-axiom-gate-open")
        self.assertTrue(payload["new_axiom_allowed_as_research"])
        self.assertFalse(payload["new_axiom_accepted"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_gates_include_residuals_and_no_fit(self) -> None:
        names = {row["gate"] for row in build_payload()["gates"]}

        self.assertIn("mathematical_consistency", names)
        self.assertIn("janus_compatibility", names)
        self.assertIn("no_fit_policy", names)
        self.assertIn("prediction_unlock", names)

    def test_rejects_independent_qcross_and_observable_fit(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("observable residual", rules)
        self.assertIn("Q_cross", rules)
        self.assertIn("Newtonian sign laws", rules)

    def test_markdown_lists_innovative_branches(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Stueckelberg", markdown)
        self.assertIn("zero-divergence K solver", markdown)
        self.assertIn("auxiliary-L", markdown)


if __name__ == "__main__":
    unittest.main()
