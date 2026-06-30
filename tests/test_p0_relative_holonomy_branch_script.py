from __future__ import annotations

import unittest

from scripts.build_p0_relative_holonomy_branch import build_payload


class P0RelativeHolonomyBranchTests(unittest.TestCase):
    def test_holonomy_branch_is_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["nonflat_branch_written"])
        self.assertTrue(payload["keeps_relative_curvature"])
        self.assertFalse(payload["path_rule_source_derived"])
        self.assertFalse(payload["zero_divergence_verified"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_construction_mentions_nonflat_path_and_same_rule(self) -> None:
        text = " ".join(build_payload()["construction"])

        self.assertIn("R_Omega != 0", text)
        self.assertIn("path dependence", text)
        self.assertIn("Q_cross and K", text)
        self.assertIn("closed loops", text)

    def test_blockers_forbid_tuned_holonomy(self) -> None:
        blockers = " ".join(build_payload()["blockers"])

        self.assertIn("source-derived path", blockers)
        self.assertIn("light path prescription", blockers)
        self.assertIn("zero-divergence PDE", blockers)
        self.assertIn("cannot be tuned", blockers)


if __name__ == "__main__":
    unittest.main()
