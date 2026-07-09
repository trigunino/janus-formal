import unittest

from src.janus_lab.janus_phase_space_occupation_search import non_throat_weyl_cusp_final_frontier_payload


class JanusNonThroatWeylCuspFinalFrontierGateTests(unittest.TestCase):
    def test_final_frontier_contracts_closed_not_solution(self):
        payload = non_throat_weyl_cusp_final_frontier_payload()
        self.assertTrue(payload["closed_without_rustine"]["global_conservation_omega_relation"])
        self.assertFalse(payload["can_solve_omega_now"])
        self.assertFalse(payload["any_internal_route_closed"])


if __name__ == "__main__":
    unittest.main()
