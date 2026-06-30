from __future__ import annotations

import unittest

from scripts.build_p0_eft_volume_lambda_orientation_closure import build_payload, render_markdown


class P0EFTVolumeLambdaOrientationClosureTests(unittest.TestCase):
    def test_lambda_sign_is_closed_but_prediction_is_not(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["normal_orientation_fixed"])
        self.assertTrue(status["jump_orientation_fixed"])
        self.assertTrue(status["boundary_action_sign_fixed"])
        self.assertTrue(status["lambda_equals_minus_four_qT_derived"])
        self.assertTrue(status["volume_identity_channel_closed"])
        self.assertFalse(status["prediction_ready"])

    def test_orientation_equation_contains_minus_sign(self) -> None:
        orientation = build_payload()["orientation"]

        self.assertEqual(orientation["result"], "lambda = -4*q_T for Delta_log_det_E != 0")
        self.assertIn("cancels the outward trace flux", orientation["boundary_action_sign"])

    def test_obligations_keep_full_run_pending(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("full RUN 1", obligations)
        self.assertIn("RUN 2", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("lambda_equals_minus_four_qT_derived: True", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
