from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_simple_branch_exclusion import build_payload


class P0EFTCMBSimpleBranchExclusionTests(unittest.TestCase):
    def test_simple_cmb_branch_is_excluded(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-simple-branch-exclusion-recorded")
        self.assertTrue(payload["route_a_free_neff_excluded"])
        self.assertTrue(payload["route_b_background_only_geff_excluded"])
        self.assertTrue(payload["coherent_immirzi_patch_simple_branch_excluded"])
        self.assertTrue(payload["cmb_simple_branch_excluded_by_planck"])

    def test_no_fit_remains_false(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertGreater(payload["best_active_patch_chi2_CMB"], 1000.0)


if __name__ == "__main__":
    unittest.main()
