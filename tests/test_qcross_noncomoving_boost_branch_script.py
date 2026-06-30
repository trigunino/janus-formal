from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_qcross_noncomoving_boost_branch import build_payload


class QCrossNonComovingBoostBranchTests(unittest.TestCase):
    def test_boost_branch_records_exact_velocity_formula(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["branch_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertEqual(
            payload["result"]["q_cross"],
            "Q_cross=gamma^2(1-beta_vec.n)^2",
        )

    def test_small_beta_expansion_matches_order_two(self) -> None:
        beta2, beta_parallel = sp.symbols("beta2 beta_parallel")
        q_cross = (1 + beta2) * (1 - 2 * beta_parallel + beta_parallel**2)
        truncated = sp.expand(q_cross).subs(beta2 * beta_parallel, 0).subs(
            beta2 * beta_parallel**2,
            0,
        )
        expected = 1 - 2 * beta_parallel + beta_parallel**2 + beta2

        self.assertEqual(sp.simplify(truncated - expected), 0)

    def test_requirements_keep_beta_source_and_bianchi_open(self) -> None:
        requirements = " ".join(build_payload()["requirements"])

        self.assertIn("beta_vec must be derived", requirements)
        self.assertIn("Q_det remains outside", requirements)
        self.assertIn("Bianchi compatibility", requirements)

    def test_rotation_role_is_recorded_as_direction_change_only(self) -> None:
        rotation = " ".join(build_payload()["rotation_role"])

        self.assertIn("R beta_minus", rotation)
        self.assertIn("R^T n_plus", rotation)


if __name__ == "__main__":
    unittest.main()
