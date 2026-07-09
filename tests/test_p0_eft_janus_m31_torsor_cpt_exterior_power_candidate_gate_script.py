import unittest

from janus_lab.janus_phase_space_occupation_search import (
    m31_torsor_cpt_exterior_power_candidate_payload,
)


class JanusM31TorsorCPTExteriorPowerCandidateGateTests(unittest.TestCase):
    def test_m31_count_matches_required_N(self):
        payload = m31_torsor_cpt_exterior_power_candidate_payload()
        construction = payload["candidate_construction"]

        self.assertEqual(payload["published_inputs"]["Janus_Lie_group_dimension"], 11)
        self.assertEqual(payload["published_inputs"]["CPT_independent_Z2_generators"], 3)
        self.assertEqual(payload["published_inputs"]["spacetime_translation_dimension"], 4)
        self.assertEqual(construction["primitive_boundary_mode_count"], 14)
        self.assertEqual(construction["sector_dimension"], 1001)
        self.assertTrue(construction["matches_required_N"])
        self.assertEqual(construction["matching_exterior_degrees"], [4, 10])

    def test_candidate_is_not_derivation(self):
        payload = m31_torsor_cpt_exterior_power_candidate_payload()
        blockers = payload["why_not_closed"]

        self.assertTrue(blockers["mixes_continuous_torsor_modes_and_discrete_CPT_generators"])
        self.assertFalse(blockers["boundary_fermionic_exterior_algebra_derived"])
        self.assertFalse(blockers["four_excitation_sector_selected"])
        self.assertFalse(blockers["exterior_power_statistics_derived"])
        self.assertEqual(payload["verdict"], "best_current_numerical_coincidence_but_not_a_derivation")


if __name__ == "__main__":
    unittest.main()
