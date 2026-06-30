from __future__ import annotations

import unittest

from scripts.build_p0_eft_boundary_run1_run2_targets import build_payload, render_markdown


class P0EFTBoundaryRun1Run2TargetsTests(unittest.TestCase):
    def test_run_targets_are_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run1_target_encoded"])
        self.assertTrue(status["run2_target_encoded"])
        self.assertFalse(status["run1_factorization_proved"])
        self.assertFalse(status["run2_commutation_proved"])
        self.assertFalse(status["run2_zero_modes_controlled"])
        self.assertFalse(status["prediction_ready"])

    def test_run1_names_residue_vanishing(self) -> None:
        run1 = build_payload()["run1"]

        self.assertIn("M_tot", run1["input_matrix"])
        self.assertIn("other basis residues vanish", run1["matching_condition"])

    def test_run2_names_aps_and_zero_modes(self) -> None:
        run2 = build_payload()["run2"]

        self.assertEqual(run2["operator"], "A_APS = gamma^n D_Sigma")
        self.assertIn("ker(A_APS)", run2["zero_mode_target"])
        self.assertIn("must be proved", run2["dS3_note"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("run1_factorization_proved: False", markdown)
        self.assertIn("prediction_ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
