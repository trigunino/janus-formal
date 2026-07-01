from __future__ import annotations

import unittest

from scripts.build_p0_eft_bao_friction_ruler_derivation import fine_scan


class P0EFTBAOFrictionRulerDerivationTests(unittest.TestCase):
    def test_friction_ruler_scan_runs(self) -> None:
        payload = fine_scan()

        self.assertEqual(payload["status"], "bao-friction-ruler-target-scored")
        self.assertTrue(payload["passes_shape_gate"])
        self.assertGreater(payload["best"]["dv_factor"], 1.0)
        self.assertLess(payload["best"]["dv_factor"], 1.1)

    def test_target_is_not_claimed_as_derived(self) -> None:
        payload = fine_scan()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertGreater(payload["effective_optical_depth"], 0.0)
        self.assertIn("tau_drag", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
