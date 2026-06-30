from __future__ import annotations

import unittest

from scripts.build_p0_eft_cayley_shell_normalization_check import build_payload, render_markdown


class P0EFTCayleyShellNormalizationCheckTests(unittest.TestCase):
    def test_finite_cayley_does_not_close_projector(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["cayley_regularization_encoded"])
        self.assertTrue(status["finite_cayley_invertibility_obstruction_recorded"])
        self.assertTrue(status["pin_minus_ratio_checked_as_projector_source"])
        self.assertFalse(status["pin_minus_ratio_alone_yields_projector"])
        self.assertFalse(status["prediction_ready"])

    def test_obstruction_is_explicit(self) -> None:
        algebra = build_payload()["algebra"]

        self.assertIn("cannot equal a rank-half projector", algebra["finite_cayley_obstruction"])
        self.assertIn("singular Cayley limit", algebra["possible_closure"])

    def test_obligations_include_boundary_equation(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("Clifford sign", obligations)
        self.assertIn("boundary Euler-Lagrange", obligations)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("pin_minus_ratio_alone_yields_projector: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
