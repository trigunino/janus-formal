from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_branch_decision import build_payload


class P0EFTCMBBranchDecisionTests(unittest.TestCase):
    def test_simple_routes_are_excluded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-branch-decision-recorded")
        self.assertTrue(payload["route_a_free_neff_excluded"])
        self.assertTrue(payload["route_b_background_only_excluded"])
        self.assertTrue(payload["cmb_requires_consistent_immirzi_perturbations"])

    def test_no_fit_ready_remains_false(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertGreater(payload["route_a_chi2_required_neff"], payload["route_a_chi2_best"])
        self.assertGreater(payload["route_b_chi2"], 2000.0)


if __name__ == "__main__":
    unittest.main()
