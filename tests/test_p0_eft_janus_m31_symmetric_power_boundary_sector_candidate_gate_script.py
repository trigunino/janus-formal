import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_symmetric_power_boundary_sector_candidate_payload,
)


class JanusM31SymmetricPowerBoundarySectorCandidateGateTests(unittest.TestCase):
    def test_symmetric_power_matches_required_N_without_CPT_mode_mixing(self):
        payload = m31_symmetric_power_boundary_sector_candidate_payload()
        construction = payload["candidate_construction"]

        self.assertEqual(payload["published_inputs"]["Janus_Lie_group_dimension"], 11)
        self.assertEqual(payload["published_inputs"]["spacetime_translation_dimension"], 4)
        self.assertEqual(construction["sector_dimension"], 1001)
        self.assertTrue(construction["matches_required_N"])
        self.assertFalse(construction["uses_CPT_discrete_labels_as_modes"])

    def test_candidate_still_needs_boundary_statistics_and_map(self):
        payload = m31_symmetric_power_boundary_sector_candidate_payload()
        blockers = payload["why_not_closed"]

        self.assertFalse(blockers["boundary_bosonic_Fock_or_symmetric_statistics_derived"])
        self.assertFalse(blockers["degree4_sector_selected_by_boundary_constraint"])
        self.assertFalse(blockers["Sym4_sector_maps_to_a_min"])
        self.assertEqual(payload["verdict"], "best_current_structural_candidate_but_not_a_derivation")


if __name__ == "__main__":
    unittest.main()
