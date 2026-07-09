import unittest

from janus_lab.janus_phase_space_occupation_search import (
    early_branch_attachment_requirements_payload,
)


class JanusEarlyBranchAttachmentRequirementsGateTests(unittest.TestCase):
    def test_late_branch_is_far_too_short_for_geometric_predrag(self):
        payload = early_branch_attachment_requirements_payload()

        self.assertLess(
            payload["geometric_redshift_requirement"]["required_a_min_over_a0"],
            0.002,
        )
        self.assertGreater(
            payload["geometric_redshift_requirement"]["late_branch_a_min_too_large_by_factor"],
            100.0,
        )

    def test_separate_early_branch_is_required_if_s4_rejected(self):
        payload = early_branch_attachment_requirements_payload()

        self.assertFalse(payload["result"]["published_late_branch_can_be_reused_alone"])
        self.assertTrue(payload["result"]["separate_early_branch_required_if_s4_rejected"])


if __name__ == "__main__":
    unittest.main()
