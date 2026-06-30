from __future__ import annotations

import unittest

from scripts.scan_p0_eft_physical_branches import evaluate_branch, scan_branches


class P0EFTPhysicalBranchScanTests(unittest.TestCase):
    def test_original_branch_is_excluded(self) -> None:
        row = evaluate_branch(4.0, 1.0, 1.0)

        self.assertFalse(row["physical"])
        self.assertLess(row["Omega_m0"], 0.05)

    def test_scan_finds_or_reports_branch(self) -> None:
        payload = scan_branches()

        self.assertIn("physical_count", payload)
        self.assertIn("first_physical_branch", payload)

    def test_if_branch_found_it_satisfies_matter_cut(self) -> None:
        first = scan_branches()["first_physical_branch"]

        if first is not None:
            self.assertGreater(first["Omega_m0"], 0.05)


if __name__ == "__main__":
    unittest.main()
