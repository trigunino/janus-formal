from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_coefficient_constraint_solver import build_payload


class P0EFTImmirziCoefficientConstraintSolverTests(unittest.TestCase):
    def test_constraint_solver_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-coefficient-constraint-solver-run")
        self.assertEqual(payload["unknowns"], 3)
        self.assertLess(payload["rank"], payload["unknowns"])
        self.assertTrue(payload["underdetermined"])

    def test_solver_does_not_claim_patch_ready(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["unique_coefficients_derived"])
        self.assertFalse(payload["cambridge_safe_to_patch"])
        self.assertEqual(payload["free_parameter"], "c_pi")


if __name__ == "__main__":
    unittest.main()
