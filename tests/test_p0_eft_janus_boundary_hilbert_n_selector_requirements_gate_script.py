import unittest

from janus_lab.janus_phase_space_occupation_search import (
    boundary_hilbert_N_selector_requirements_payload,
)


class JanusBoundaryHilbertNSelectorRequirementsGateTests(unittest.TestCase):
    def test_required_spin_and_level_are_fixed_by_N(self):
        payload = boundary_hilbert_N_selector_requirements_payload()

        self.assertEqual(payload["required_N"], 1001)
        self.assertEqual(payload["required_CP1_spin_j"], 500.0)
        self.assertEqual(payload["required_KKS_or_CS_level"], 1000)

    def test_repo_anchor_exists_but_sector_selection_missing(self):
        payload = boundary_hilbert_N_selector_requirements_payload()

        self.assertTrue(payload["existing_repo_anchor"]["CP1_candidate_exists"])
        self.assertTrue(payload["existing_repo_anchor"]["KKS_symbolic_period_exists"])
        self.assertFalse(payload["existing_repo_anchor"]["sector_selection_law_derived"])


if __name__ == "__main__":
    unittest.main()
