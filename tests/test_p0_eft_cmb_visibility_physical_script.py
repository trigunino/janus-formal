from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_visibility_physical import build_payload


class P0EFTCMBVisibilityPhysicalTests(unittest.TestCase):
    def test_visibility_target_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-visibility-physical-target-derived")
        self.assertTrue(payload["visibility_function_ready"])
        self.assertAlmostEqual(payload["normalization"], 1.0, places=6)

    def test_full_recombination_solver_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_full_recombination_solver"])
        self.assertIn("recombination ODE", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
