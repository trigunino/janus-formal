from __future__ import annotations

import unittest

from scripts.build_p0_flrw_zero_divergence_toy_solution import build_payload


class P0FlrwZeroDivergenceToySolutionTests(unittest.TestCase):
    def test_toy_branch_closes_but_not_generic_physics(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["toy_branch_closed"])
        self.assertFalse(payload["generic_physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_plus_and_minus_weights_are_cubic(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["plus_solution"]["combined_weight"],
            "B_plus k_plus proportional (a_minus/a_plus)^3",
        )
        self.assertEqual(
            payload["minus_solution"]["combined_weight"],
            "B_minus k_minus proportional (a_plus/a_minus)^3",
        )

    def test_determinant_split_keeps_transport_factor_separate(self) -> None:
        split = " ".join(build_payload()["determinant_split"])

        self.assertIn("k_plus proportional", split)
        self.assertIn("3-n", split)
        self.assertIn("n=4", split)
        self.assertIn("combined B*k remains cubic", split)
        self.assertIn("not an optical Q_cross amplitude", split)

    def test_not_closed_lists_generic_blockers(self) -> None:
        not_closed = " ".join(build_payload()["not_closed"])

        self.assertIn("non-comoving perturbations", not_closed)
        self.assertIn("F_alpha", not_closed)
        self.assertIn("Pi", not_closed)
        self.assertIn("Q_cross", not_closed)

    def test_assumptions_include_aligned_tetrads_and_dust(self) -> None:
        assumptions = " ".join(build_payload()["assumptions"])

        self.assertIn("dust only", assumptions)
        self.assertIn("L_minus_to_plus=I", assumptions)
        self.assertIn("dot(rho_s)+3 H_s rho_s=0", assumptions)


if __name__ == "__main__":
    unittest.main()
