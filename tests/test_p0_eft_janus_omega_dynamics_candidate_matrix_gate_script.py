import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    omega_dynamics_candidate_matrix_payload,
)


class JanusOmegaDynamicsCandidateMatrixGateTests(unittest.TestCase):
    def test_conformal_einstein_trace_is_first(self):
        payload = omega_dynamics_candidate_matrix_payload()
        self.assertEqual(payload["recommended_next"], "ConformalEinsteinTrace")
        self.assertEqual(payload["candidates"][0]["name"], "ConformalEinsteinTrace")


if __name__ == "__main__":
    unittest.main()
