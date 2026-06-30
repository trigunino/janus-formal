from __future__ import annotations

import unittest

from scripts.build_p0_eft_slip_green_neumann_bridge import build_payload, render_markdown


class P0EFTSlipGreenNeumannBridgeTests(unittest.TestCase):
    def test_value_slip_is_conditional_on_green_kernel(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["neumann_green_bridge_encoded"])
        self.assertTrue(status["target_kernel_identified"])
        self.assertFalse(status["green_kernel_computed"])
        self.assertTrue(status["value_slip_derived_conditionally"])
        self.assertFalse(status["lensing_source_closed"])

    def test_safe_result_is_derivative_jump(self) -> None:
        detail = build_payload()["status_detail"]

        self.assertIn("derivative slip jump", detail["safe_result"])
        self.assertIn("not computed", detail["not_done"])

    def test_obligations_include_kernel_computation(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("compute the dS3", obligations)
        self.assertIn("update the slip coefficient", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("green_kernel_computed: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
