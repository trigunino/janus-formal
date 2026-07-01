from __future__ import annotations

import unittest

from scripts.build_p0_eft_residual_factor_geometric_origin import build_payload


class P0EFTResidualFactorGeometricOriginTests(unittest.TestCase):
    def test_origin_scan_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "residual-factor-geometric-origin-scored")
        self.assertIn("best_candidate", payload)
        self.assertGreater(len(payload["candidates"]), 1)

    def test_origin_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertIn("denominator 50", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
