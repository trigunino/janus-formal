from __future__ import annotations

import unittest

from scripts.build_p0_gauge_lifting_decision_matrix import build_payload


class P0GaugeLiftingDecisionMatrixTests(unittest.TestCase):
    def test_matrix_is_ranked_but_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["branches_ranked"])
        self.assertIsNone(payload["accepted_branch"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_branches_include_pi_boundary_and_action(self) -> None:
        branches = {row["branch"] for row in build_payload()["branches"]}

        self.assertIn("Pi eigenframe", branches)
        self.assertIn("boundary/initial L", branches)
        self.assertIn("action/gauge principle", branches)

    def test_boundary_branch_is_first_priority(self) -> None:
        branches = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertEqual(branches["boundary/initial L"]["priority"], 1)
        self.assertFalse(branches["boundary/initial L"]["accepted"])

    def test_next_steps_search_sources_then_axioms(self) -> None:
        steps = " ".join(build_payload()["immediate_next"])

        self.assertIn("boundary/initial L", steps)
        self.assertIn("Pi evolution", steps)
        self.assertIn("action/gauge", steps)
        self.assertIn("prediction_ready=false", steps)


if __name__ == "__main__":
    unittest.main()
