import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    weyl_cusp_pt_boundary_clock_route_payload,
)


class JanusWeylCuspPTBoundaryClockRouteGateTests(unittest.TestCase):
    def test_weyl_cusp_solves_domain_not_dynamics(self):
        payload = weyl_cusp_pt_boundary_clock_route_payload()
        self.assertTrue(payload["domain_problem_solved"])
        self.assertFalse(payload["dynamics_problem_solved"])
        self.assertFalse(payload["closed_now"])

    def test_physical_clock_is_the_blocker(self):
        payload = weyl_cusp_pt_boundary_clock_route_payload()
        self.assertFalse(payload["checks"]["physical_clock_law_derived"])
        self.assertIn("Weyl cusp is gauge", payload["hard_blocker"])


if __name__ == "__main__":
    unittest.main()
