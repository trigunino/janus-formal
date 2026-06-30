from __future__ import annotations

import unittest

from scripts.build_p0_eft_spin_holonomy_obligation import build_payload, render_markdown


class P0EFTSpinHolonomyObligationTests(unittest.TestCase):
    def test_spin_holonomy_is_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["spin_holonomy_obligation_written"])
        self.assertFalse(status["pt_spin_lift_proved"])
        self.assertFalse(status["q_A_geometrically_fixed"])
        self.assertFalse(status["prediction_ready"])

    def test_consequence_fixes_qA_if_proved(self) -> None:
        consequence = build_payload()["consequence_if_proved"]

        self.assertEqual(consequence["q_T"], "1")
        self.assertEqual(consequence["q_A"], "sign(Sigma)/sqrt(6)")
        self.assertEqual(consequence["branch"], "R_paired_axial_trace")

    def test_obligations_include_spin_lift_and_pairing(self) -> None:
        obligations = " ".join(row["statement"] for row in build_payload()["obligations"])

        self.assertIn("spin bundle", obligations)
        self.assertIn("chiral holonomy", obligations)
        self.assertIn("parity-odd axial residues", obligations)

    def test_markdown_keeps_eft_parameter_warning(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("q_A remains an EFT parameter", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
