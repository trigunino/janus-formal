from __future__ import annotations

import unittest

from scripts.build_p0_eft_pt_spin_lift_derivation import build_payload, render_markdown


class P0EFTPTSpinLiftDerivationTests(unittest.TestCase):
    def test_derivation_blocks_on_pin_choice(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["pt_frame_action_identified"])
        self.assertFalse(status["spin_or_pin_lift_chosen"])
        self.assertFalse(status["chirality_holonomy_derived"])
        self.assertFalse(status["q_A_fixed"])
        self.assertFalse(status["prediction_ready"])

    def test_obstruction_is_metric_insufficient(self) -> None:
        obstruction = build_payload()["obstruction"]

        self.assertTrue(obstruction["cannot_be_inferred_from_metric_only"])
        self.assertIn("Pin+/Pin-", obstruction["missing_choice"])

    def test_consequence_if_closed_names_qA(self) -> None:
        consequence = build_payload()["consequence_if_closed"]

        self.assertEqual(consequence["q_A"], "sign(Sigma)/sqrt(6)")
        self.assertEqual(consequence["q_T"], "1")

    def test_markdown_keeps_blocker_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("blocked-on-pin-structure-choice", markdown)
        self.assertIn("q_A_fixed: False", markdown)


if __name__ == "__main__":
    unittest.main()
