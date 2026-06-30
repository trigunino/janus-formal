from __future__ import annotations

import unittest

from scripts.build_p0_flat_vs_holonomy_decision import build_payload


class P0FlatVsHolonomyDecisionTests(unittest.TestCase):
    def test_decision_is_written_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["decision_written"])
        self.assertIsNone(payload["accepted_branch"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_both_branches_are_present(self) -> None:
        branches = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertIn("pure_gauge_flat", branches)
        self.assertIn("relative_holonomy_nonflat", branches)
        self.assertIn("R_Omega=0", " ".join(branches["pure_gauge_flat"]["must_prove"]))
        self.assertIn("source path rule", " ".join(branches["relative_holonomy_nonflat"]["must_prove"]))

    def test_decision_rule_prefers_flat_then_holonomy(self) -> None:
        rule = " ".join(build_payload()["decision_rule"])

        self.assertIn("start with pure_gauge_flat", rule)
        self.assertIn("reject flat branch", rule)
        self.assertIn("promote holonomy branch only", rule)
        self.assertIn("K/Qcross consistency", rule)


if __name__ == "__main__":
    unittest.main()
