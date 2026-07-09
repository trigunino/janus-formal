import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    current_branch_early_late_matching_final_pass_payload,
)


class JanusCurrentBranchEarlyLateMatchingFinalPassGateTests(unittest.TestCase):
    def test_current_branch_remains_unclosed(self):
        payload = current_branch_early_late_matching_final_pass_payload()
        self.assertFalse(payload["closed_now"])
        self.assertFalse(payload["no_fit_closed_now"])
        self.assertEqual(payload["recommended_next_branch"], "JanusProjectivePointPTLimit")

    def test_hard_blockers_are_explicit(self):
        payload = current_branch_early_late_matching_final_pass_payload()
        blockers = " ".join(payload["hard_blockers_remaining"])
        self.assertIn("early H_J(a)", blockers)
        self.assertIn("transition surface", blockers)


if __name__ == "__main__":
    unittest.main()
