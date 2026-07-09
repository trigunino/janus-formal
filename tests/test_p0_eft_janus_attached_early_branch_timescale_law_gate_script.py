import unittest

from janus_lab.janus_phase_space_occupation_search import (
    attached_early_branch_timescale_law_payload,
)


class JanusAttachedEarlyBranchTimescaleLawGateTests(unittest.TestCase):
    def test_timescale_ratio_is_fixed_by_c1_geometry(self):
        payload = attached_early_branch_timescale_law_payload()

        self.assertTrue(payload["result"]["time_scale_ratio_geometrically_fixed_after_inputs"])
        self.assertTrue(payload["result"]["new_free_ratio_removed"])
        self.assertAlmostEqual(
            payload["values"]["exact_time_scale_ratio"],
            payload["values"]["diagnostic_time_scale_ratio"],
            places=10,
        )

    def test_remaining_freedom_is_input_selection_not_ratio(self):
        payload = attached_early_branch_timescale_law_payload()

        self.assertTrue(payload["result"]["a_min_selection_still_open"])
        self.assertTrue(payload["result"]["transition_selection_still_open"])
        self.assertFalse(payload["result"]["physical_model_ready"])


if __name__ == "__main__":
    unittest.main()
