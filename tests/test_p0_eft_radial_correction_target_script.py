from __future__ import annotations

import unittest

from scripts.build_p0_eft_radial_correction_target import build_payload


class P0EFTRadialCorrectionTargetTests(unittest.TestCase):
    def test_radial_correction_target_scores(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "radial-correction-target-scored")
        self.assertGreater(payload["baseline_no_radial_correction"]["chi2"], 0.0)
        self.assertGreater(payload["linear_target_score"]["chi2"], 0.0)

    def test_target_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertIn("derive", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
