import unittest

from janus_lab.janus_phase_space_occupation_search import (
    hnormal_symmetry_breaking_candidate_matrix_payload,
)


class JanusHnormalSymmetryBreakingCandidateMatrixGateTests(unittest.TestCase):
    def test_pt_normal_is_recommended_but_not_closed(self):
        payload = hnormal_symmetry_breaking_candidate_matrix_payload()

        self.assertEqual(payload["recommended_attack"], "PT_normal_generator_to_internal_Sym4_matrix")
        self.assertEqual(payload["admissible_closers_now"], [])
        self.assertFalse(payload["no_fit_closed_now"])

    def test_componentwise_direction_is_rejected_as_unanchored(self):
        payload = hnormal_symmetry_breaking_candidate_matrix_payload()
        rows = {row["name"]: row for row in payload["candidates"]}

        self.assertFalse(rows["componentwise_triplet_direction"]["janus_anchored"])
        self.assertTrue(rows["componentwise_triplet_direction"]["defines_operator_now"])
        self.assertEqual(payload["if_recommended_attack_closes"]["z_max"], 1000.0)


if __name__ == "__main__":
    unittest.main()
