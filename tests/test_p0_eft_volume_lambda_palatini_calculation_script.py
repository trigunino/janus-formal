from __future__ import annotations

import unittest

from scripts.build_p0_eft_volume_lambda_palatini_calculation import build_payload, render_markdown


class P0EFTVolumeLambdaPalatiniCalculationTests(unittest.TestCase):
    def test_palatini_derives_delta_and_factor_four(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["palatini_volume_variation_performed"])
        self.assertTrue(status["delta_source_extracted"])
        self.assertTrue(status["factor_four_derived_from_dirac_dimension"])
        self.assertTrue(status["lambda_magnitude_fixed"])
        self.assertFalse(status["lambda_equals_minus_four_qT_fully_derived"])
        self.assertFalse(status["prediction_ready"])

    def test_sign_orientation_remains_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["theorem_status"]["lambda_sign_requires_orientation_convention"])
        self.assertIn("orientation", payload["sign_audit"]["sign_depends_on"])
        self.assertIn("lambda = -4*q_T", payload["sign_audit"]["derived_if_delta_nonzero"])

    def test_obligations_are_orientation_only(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("boundary action orientation", obligations)
        self.assertIn("normal orientation", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("lambda-magnitude-derived-sign-orientation-open", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
