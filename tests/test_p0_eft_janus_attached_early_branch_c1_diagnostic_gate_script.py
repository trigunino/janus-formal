import unittest

from janus_lab.janus_phase_space_occupation_search import (
    attached_early_branch_c1_diagnostic_payload,
)


class JanusAttachedEarlyBranchC1DiagnosticGateTests(unittest.TestCase):
    def test_c1_attachment_is_geometrically_possible(self):
        payload = attached_early_branch_c1_diagnostic_payload()

        self.assertTrue(payload["result"]["C0_match_possible"])
        self.assertTrue(payload["result"]["C1_H_match_possible"])
        self.assertGreater(payload["early_branch"]["time_scale_ratio_needed"], 0.0)

    def test_attachment_is_not_physical_model_until_source_derived(self):
        payload = attached_early_branch_c1_diagnostic_payload()

        self.assertTrue(payload["result"]["requires_new_time_scale_or_state_constant"])
        self.assertFalse(payload["result"]["source_derived"])
        self.assertFalse(payload["result"]["physical_model_ready"])


if __name__ == "__main__":
    unittest.main()
