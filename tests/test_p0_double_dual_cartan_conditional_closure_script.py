from __future__ import annotations

import unittest

from scripts.build_p0_double_dual_cartan_conditional_closure import build_payload, render_markdown


class P0DoubleDualCartanConditionalClosureTests(unittest.TestCase):
    def test_route_is_conditional_not_unconditional(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["conditional_closure_proved"])
        self.assertFalse(status["unconditional_janus_closure_proved"])
        self.assertTrue(status["new_axiom"])
        self.assertFalse(status["prediction_ready"])
        self.assertTrue(status["conditional_prediction_ready_path_open"])

    def test_axiom_is_explicit(self) -> None:
        payload = build_payload()
        assumptions = " ".join(row["id"] + " " + row["statement"] for row in payload["assumptions"])

        self.assertIn("A_DoubleDualCartanSource", assumptions)
        self.assertIn("double-dual curvature-torsion invariant", assumptions)
        self.assertIn("A_HorndeskiBoundaryCompletion", assumptions)

    def test_chain_reaches_stability(self) -> None:
        chain = " ".join(build_payload()["chain"])

        self.assertIn("Horndeski-radion bulk coupling", chain)
        self.assertIn("k2 and k4 contact closure", chain)
        self.assertIn("dS scalar", chain)

    def test_markdown_does_not_hide_new_axiom(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("new_axiom: True", markdown)
        self.assertIn("prediction_ready: False", markdown)
        self.assertIn("A_DoubleDualCartanSource", markdown)


if __name__ == "__main__":
    unittest.main()
