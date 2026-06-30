from __future__ import annotations

import unittest

from scripts.build_p0_eft_ec_normalization_branch import build_payload, render_markdown


class P0EFTECNormalizationBranchTests(unittest.TestCase):
    def test_ec_branch_fixes_ctorsion_in_branch_only(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["ec_no_holst_branch_encoded"])
        self.assertTrue(status["C_EC_fixed_in_this_convention"])
        self.assertEqual(status["C_EC_value"], "23/6")
        self.assertTrue(status["alpha_iso_ready_in_ec_branch"])
        self.assertFalse(status["prediction_ready_unconditional"])

    def test_alpha_iso_value_is_recorded(self) -> None:
        coefficient = build_payload()["coefficient"]

        self.assertIn("161/36", coefficient["alpha_iso"])
        self.assertIn("-23/6", coefficient["raw_quadratic"])

    def test_convention_warning_is_explicit(self) -> None:
        action = build_payload()["action"]

        self.assertIn("no Holst", action["branch"])
        self.assertIn("rescale C_EC", action["convention_warning"])

    def test_markdown_keeps_unconditional_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("C_EC-fixed-for-standard-EC-branch", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
