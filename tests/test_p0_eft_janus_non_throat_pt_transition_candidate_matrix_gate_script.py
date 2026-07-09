import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    non_throat_pt_transition_candidate_matrix_payload,
)


class JanusNonThroatPTTransitionCandidateMatrixGateTests(unittest.TestCase):
    def test_conformal_boundary_is_first_candidate(self):
        payload = non_throat_pt_transition_candidate_matrix_payload()
        self.assertEqual(payload["recommended_first"], "ConformalPTBoundary")
        self.assertEqual(payload["candidates"][0]["name"], "ConformalPTBoundary")

    def test_all_candidates_avoid_sigma_radius(self):
        payload = non_throat_pt_transition_candidate_matrix_payload()
        self.assertTrue(all(row["avoids_sigma_radius"] for row in payload["candidates"]))


if __name__ == "__main__":
    unittest.main()
