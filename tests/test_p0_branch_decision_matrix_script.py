from __future__ import annotations

import unittest

from scripts.build_p0_branch_decision_matrix import build_payload


class P0BranchDecisionMatrixTests(unittest.TestCase):
    def test_primary_branch_is_minimal_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["primary_branch"], "lorentz_dust_plus_fermi_walker")
        self.assertFalse(payload["primary_branch_prediction_ready"])
        self.assertEqual(payload["status"], "decision-matrix-open")

    def test_rejects_naive_and_determinant_copy(self) -> None:
        branches = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertEqual(branches["naive_copied_stress"]["rank"], "reject")
        self.assertEqual(branches["determinant_weighted_copy"]["rank"], "reject")
        self.assertIn("double-counting", branches["determinant_weighted_copy"]["next_action"])

    def test_prioritizes_fermi_walker_dust(self) -> None:
        branches = {row["branch"]: row for row in build_payload()["branches"]}
        primary_route = " ".join(build_payload()["primary_route"])

        self.assertEqual(branches["lorentz_dust_plus_fermi_walker"]["rank"], "primary")
        self.assertIn("receiver-geodesic", primary_route)
        self.assertIn("B_plus/B_minus", primary_route)
        self.assertIn("R_plus=0 and R_minus=0", primary_route)

    def test_escalation_rules_block_patches(self) -> None:
        rules = " ".join(build_payload()["escalation_rules"])

        self.assertIn("only if pressure appears", rules)
        self.assertIn("do not add Pi merely to fix gauge freedom", rules)
        self.assertIn("without independent source principle", rules)


if __name__ == "__main__":
    unittest.main()
