from __future__ import annotations

import unittest

from scripts.build_p0_eft_loop_double_dual_conditional import build_payload, render_markdown


class P0EFTLoopDoubleDualConditionalTests(unittest.TestCase):
    def test_eft_route_is_encoded_but_not_prediction_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["eft_route_encoded"])
        self.assertFalse(status["heat_kernel_calculation_done"])
        self.assertTrue(status["conditional_closure_proved_if_obligations_hold"])
        self.assertFalse(status["unconditional_janus_closure_proved"])
        self.assertFalse(status["prediction_ready"])

    def test_not_classical_rustine_but_quantum_obligation(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["new_classical_rustine"])
        self.assertTrue(status["quantum_eft_obligation"])

    def test_obligations_name_heat_kernel_and_projection(self) -> None:
        obligations = " ".join(row["statement"] for row in build_payload()["obligations"])

        self.assertIn("heat-kernel", obligations)
        self.assertIn("project out non-Horndeski", obligations)
        self.assertIn("stable under renormalization", obligations)

    def test_markdown_keeps_prediction_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("prediction_ready: False", markdown)
        self.assertIn("heat_kernel_calculation_done: False", markdown)


if __name__ == "__main__":
    unittest.main()
