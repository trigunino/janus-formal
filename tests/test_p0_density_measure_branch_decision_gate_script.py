from __future__ import annotations

import unittest

from scripts.build_p0_density_measure_branch_decision_gate import build_payload


class P0DensityMeasureBranchDecisionGateTests(unittest.TestCase):
    def test_branch_decision_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "density-measure-branch-decision-open")
        self.assertIsNone(payload["selected_branch"])
        self.assertFalse(payload["branch_decision_closed"])
        self.assertFalse(payload["effective_density_continuity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_branches_cover_4volume_3volume_and_effective_density(self) -> None:
        branches = {row["branch"] for row in build_payload()["branches"]}

        self.assertIn("field_equation_4volume", branches)
        self.assertIn("dust_flux_3volume", branches)
        self.assertIn("effective_density_absorbs_B", branches)

    def test_acceptance_keeps_qdet_qcross_and_continuity_separate(self) -> None:
        acceptance = " ".join(build_payload()["acceptance"])

        self.assertIn("one branch selected", acceptance)
        self.assertIn("B/J_phi", acceptance)
        self.assertIn("Q_det", acceptance)
        self.assertIn("Q_cross", acceptance)
        self.assertIn("D_receiver", acceptance)


if __name__ == "__main__":
    unittest.main()
