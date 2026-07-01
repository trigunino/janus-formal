from __future__ import annotations

import unittest

from scripts.build_p0_eft_combined_primordial_sector_target import build_payload


class P0EFTCombinedPrimordialSectorTargetTests(unittest.TestCase):
    def test_required_correction_is_not_small(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "combined-primordial-sector-target-recorded")
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertGreater(payload["required_highl_plus_lowE_suppression_fraction"], 0.9)

    def test_strict_budget_already_blocked_by_other_channels(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["non_highl_lowE_floor"], payload["target_chi2"])
        self.assertFalse(payload["strict_target_possible_without_lowlTT_lensing_work"])


if __name__ == "__main__":
    unittest.main()
