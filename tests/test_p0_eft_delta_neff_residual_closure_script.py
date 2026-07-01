from __future__ import annotations

import unittest

from scripts.build_p0_eft_delta_neff_residual_closure import build_payload


class P0EFTDeltaNeffResidualClosureTests(unittest.TestCase):
    def test_residual_closure_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "delta-neff-residual-closure-attempted")
        self.assertGreater(payload["exact_required_factor"], 1.0)
        self.assertIn("best_candidate", payload)

    def test_residual_is_not_claimed_as_derived(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_derived_geometry"])
        self.assertGreater(payload["exact_required_fractional_correction"], 0.0)


if __name__ == "__main__":
    unittest.main()
