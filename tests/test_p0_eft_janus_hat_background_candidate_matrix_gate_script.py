import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    hat_background_candidate_matrix_payload,
)


class JanusHatBackgroundCandidateMatrixGateTests(unittest.TestCase):
    def test_projective_background_ranked_first(self):
        payload = hat_background_candidate_matrix_payload()
        self.assertEqual(payload["recommended_next"], "ProjectiveS4RP4ConformalBackground")
        self.assertEqual(payload["candidates"][0]["name"], "ProjectiveS4RP4ConformalBackground")


if __name__ == "__main__":
    unittest.main()
