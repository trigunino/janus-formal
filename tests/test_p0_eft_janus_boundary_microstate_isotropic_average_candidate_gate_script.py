import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    boundary_microstate_isotropic_average_candidate_payload,
)


class JanusBoundaryMicrostateIsotropicAverageCandidateGateTests(unittest.TestCase):
    def test_microstates_reach_pre_drag_but_macro_profiles_do_not(self):
        payload = boundary_microstate_isotropic_average_candidate_payload()
        self.assertEqual(payload["counts"]["microstate_count"], 1001)
        self.assertEqual(payload["counts"]["macro_isotropic_profile_count"], 70)
        self.assertTrue(payload["counts"]["microstates_reach_pre_drag"])
        self.assertFalse(payload["counts"]["macro_profiles_reach_pre_drag"])

    def test_hard_conditions_are_not_claimed(self):
        payload = boundary_microstate_isotropic_average_candidate_payload()
        self.assertFalse(payload["hard_conditions"]["boundary_density_matrix_SO3_invariant"])
        self.assertFalse(payload["hard_conditions"]["early_ruler_uses_microstate_count_not_macro_profiles"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
