from __future__ import annotations

import unittest

from scripts.build_p0_eft_volume_lambda_derivation_target import build_payload, render_markdown


class P0EFTVolumeLambdaDerivationTargetTests(unittest.TestCase):
    def test_lambda_target_is_encoded_not_derived(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["volume_jump_mechanism_encoded"])
        self.assertTrue(status["lambda_target_encoded"])
        self.assertTrue(status["factor_four_audit_encoded"])
        self.assertFalse(status["palatini_variation_performed"])
        self.assertFalse(status["lambda_equals_minus_four_qT_derived"])
        self.assertFalse(status["prediction_ready"])

    def test_factor_four_sources_are_audited(self) -> None:
        audit = build_payload()["factor_four_audit"]

        self.assertIn("tr(I_4)=4", audit["allowed_sources"])
        self.assertIn("four-dimensional tetrad volume variation", audit["allowed_sources"])
        self.assertIn("manual insertion", audit["forbidden_source"])

    def test_obligations_require_identity_not_parameter_solve(self) -> None:
        obligations = " ".join(build_payload()["obligations"])

        self.assertIn("Palatini", obligations)
        self.assertIn("lambda + 4*q_T = 0 as an identity", obligations)

    def test_markdown_keeps_ready_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("lambda_equals_minus_four_qT_derived: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
