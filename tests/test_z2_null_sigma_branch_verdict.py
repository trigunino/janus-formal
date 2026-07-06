from __future__ import annotations

import unittest

from src.janus_lab.z2_null_sigma_branch_verdict import (
    null_sigma_branch_verdict_payload,
)


class Z2NullSigmaBranchVerdictTests(unittest.TestCase):
    def test_null_branch_is_exhausted_but_not_promoted(self) -> None:
        payload = null_sigma_branch_verdict_payload()

        self.assertTrue(payload["verdict"]["null_branch_exhausted_without_sparadrap"])
        self.assertFalse(payload["verdict"]["promote_null_shell_model"])
        self.assertFalse(payload["null_branch_closure"]["null_junction_balance_ready"])

    def test_chapter_6_7_route_reopens_regular_surface(self) -> None:
        metric = null_sigma_branch_verdict_payload()["source_consistency_frontier"][
            "chapter_6_7_metric_at_r_equals_a"
        ]

        self.assertEqual(metric["g_tt"], 2.0)
        self.assertEqual(metric["det_tr_block"], -1.0)
        self.assertFalse(metric["induced_surface_degenerate"])


if __name__ == "__main__":
    unittest.main()
