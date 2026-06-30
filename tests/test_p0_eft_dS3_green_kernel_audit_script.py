from __future__ import annotations

import unittest

from scripts.build_p0_eft_dS3_green_kernel_audit import build_payload, render_markdown


class P0EFTDS3GreenKernelAuditTests(unittest.TestCase):
    def test_kink_ready_but_value_green_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["spectral_operator_defined"])
        self.assertTrue(status["mass_gap_identified"])
        self.assertTrue(status["kink_only_observable_ready_conditionally"])
        self.assertTrue(status["coincident_green_requires_regularization"])
        self.assertFalse(status["green_kernel_equals_three_halves_H_proved"])
        self.assertFalse(status["value_slip_ready"])

    def test_coincident_limit_warns_regularization(self) -> None:
        spectral = build_payload()["spectral"]

        self.assertIn("regularization", spectral["coincident_limit"])
        self.assertIn("(3/2)H", spectral["target"])

    def test_obligations_keep_kink_safe_branch(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("Green regularization", obligations)
        self.assertIn("kink-only lensing", obligations)

    def test_markdown_keeps_value_not_ready(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("value_slip_ready: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
