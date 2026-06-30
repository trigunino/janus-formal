from __future__ import annotations

import unittest

from scripts.build_p0_b4vol_fminimal_residual_trial import build_payload


class P0B4volFminimalResidualTrialTests(unittest.TestCase):
    def test_trial_reduces_but_does_not_close(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-trial-open")
        self.assertTrue(payload["b4vol_branch_selected_for_trial"])
        self.assertTrue(payload["fminimal_branch_selected_for_trial"])
        self.assertTrue(payload["dust_trial_reduced"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_residual_rows_track_conditional_and_open_terms(self) -> None:
        rows = {row["term"]: row for row in build_payload()["residual_rows"]}

        self.assertEqual(rows["D_phi density + D log B_4vol"]["status"], "conditional")
        self.assertEqual(rows["D_L velocity/tetrad flow projection"]["status"], "conditional")
        self.assertEqual(rows["C_self-other u_to u_to"]["status"], "open")
        self.assertEqual(rows["mirror plus/minus inverse consistency"]["status"], "open")

    def test_blockers_keep_real_closure_open(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("D_receiver(B_4vol rho_to u_to)=0", blockers)
        self.assertIn("minimal-gauge F_alpha is not source-derived", blockers)
        self.assertIn("hE=rho hCuu", blockers)
        self.assertIn("pressure/Pi", blockers)


if __name__ == "__main__":
    unittest.main()
