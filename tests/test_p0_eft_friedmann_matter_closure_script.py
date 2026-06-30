from __future__ import annotations

import unittest

from scripts.build_p0_eft_friedmann_matter_closure import build_payload, derive_omega_m0


class P0EFTFriedmannMatterClosureTests(unittest.TestCase):
    def test_friedmann_sum_is_unity(self) -> None:
        closure = derive_omega_m0()

        self.assertAlmostEqual(closure["friedmann_sum"], 1.0)

    def test_omega_m0_is_derived_not_fixed_to_point_three(self) -> None:
        closure = derive_omega_m0()

        self.assertIn("Omega_m0=1", closure["closure_formula"])
        self.assertNotEqual(round(closure["Omega_m0"], 6), 0.3)

    def test_positive_branch_status_is_explicit(self) -> None:
        payload = build_payload()

        self.assertIn("positive_matter_branch", payload["theorem_status"])
        self.assertTrue(payload["theorem_status"]["Omega_m0_derived_from_branch"])


if __name__ == "__main__":
    unittest.main()
