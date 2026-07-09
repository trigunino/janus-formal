import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    conformal_einstein_trace_reduction_payload,
)


class JanusConformalEinsteinTraceReductionGateTests(unittest.TestCase):
    def test_symbolic_reduction_closed_not_active_solution(self):
        payload = conformal_einstein_trace_reduction_payload()
        self.assertTrue(payload["symbolic_reduction_closed"])
        self.assertFalse(payload["active_solution_closed"])
        self.assertIn("R_hat", payload["trace_reduction"]["omega_equation"])


if __name__ == "__main__":
    unittest.main()
