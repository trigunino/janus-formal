from __future__ import annotations

import unittest

from scripts.build_p0_eft_dv_ruler_residual_target import run_scan


class P0EFTDVRulerResidualTargetTests(unittest.TestCase):
    def test_dv_ruler_scan_runs(self) -> None:
        payload = run_scan()

        self.assertEqual(payload["status"], "dv-ruler-residual-target-scored")
        self.assertGreater(len(payload["rows"]), 1)
        self.assertIn("best", payload)

    def test_target_is_not_claimed_as_derived(self) -> None:
        payload = run_scan()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertIn("ruler", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
