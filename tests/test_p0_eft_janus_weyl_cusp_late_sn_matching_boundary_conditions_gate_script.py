import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    weyl_cusp_late_sn_matching_boundary_conditions_payload,
)


class JanusWeylCuspLateSNMatchingBoundaryConditionsGateTests(unittest.TestCase):
    def test_boundary_problem_formulated_not_solved(self):
        payload = weyl_cusp_late_sn_matching_boundary_conditions_payload()
        self.assertTrue(payload["boundary_problem_closed"])
        self.assertFalse(payload["matching_solution_closed"])
        self.assertIn("Omega -> 1", payload["boundary_conditions"]["late_sn_recovery"])


if __name__ == "__main__":
    unittest.main()
