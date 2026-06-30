from __future__ import annotations

import unittest

from scripts.build_p0_b_jphi_qdet_source_measure_branch_selection_target import build_payload


class P0BJphiQdetSourceMeasureBranchSelectionTargetTests(unittest.TestCase):
    def test_branch_selection_is_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-measure-branch-selection-open")
        self.assertIsNone(payload["selected_branch"])
        self.assertFalse(payload["source_traceability_closed"])
        self.assertFalse(payload["bianchi_after_selection_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_three_measure_branches_are_candidates(self) -> None:
        branches = {row["branch"] for row in build_payload()["branches"]}

        self.assertEqual(
            branches,
            {
                "field_equation_4volume_source",
                "slice_dust_flux_source",
                "effective_density_source",
            },
        )

    def test_acceptance_prevents_double_count_and_qcross_merge(self) -> None:
        acceptance = " ".join(build_payload()["acceptance"])

        self.assertIn("exactly one active convention", acceptance)
        self.assertIn("no Q_det double count", acceptance)
        self.assertIn("Q_cross remains optical", acceptance)
        self.assertIn("lapse/slice", acceptance)
        self.assertIn("Bianchi residual", acceptance)


if __name__ == "__main__":
    unittest.main()
