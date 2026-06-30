from __future__ import annotations

import unittest

from scripts.build_bianchi_closure_target import build_payload


class BianchiClosureTargetTests(unittest.TestCase):
    def test_exact_branch_stays_blocked(self) -> None:
        payload = build_payload()
        branches = {row["branch"]: row for row in payload["branches"]}

        self.assertEqual(branches["weak_field_newtonian"]["status"], "accepted-diagnostic")
        self.assertEqual(branches["exact_mixed_stress_tensor"]["status"], "not-closed")

    def test_both_sector_constraints_block_tensor_lensing(self) -> None:
        payload = build_payload()

        self.assertEqual(len(payload["constraints"]), 2)
        self.assertTrue(all(row["blocks_tensor_lensing"] for row in payload["constraints"]))


if __name__ == "__main__":
    unittest.main()
