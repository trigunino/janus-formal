from __future__ import annotations

import unittest

from scripts.build_p0_eft_holst_plasma_relation_lock import build_payload


class P0EFTHolstPlasmaRelationLockTests(unittest.TestCase):
    def test_relation_lock_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "holst-plasma-relation-lock-scored")
        self.assertTrue(payload["passes_bao_shape_gate"])
        self.assertLess(abs(payload["chi2_penalty_vs_exact"]), 1.0)

    def test_relation_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertFalse(payload["micro_residual_is_phenomenologically_critical"])


if __name__ == "__main__":
    unittest.main()
