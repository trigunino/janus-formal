import unittest

from src.janus_lab.janus_phase_space_occupation_search import omega_00_solvability_frontier_payload


class JanusOmega00SolvabilityFrontierGateTests(unittest.TestCase):
    def test_frontier_closes_contract_not_solution(self):
        payload = omega_00_solvability_frontier_payload()
        self.assertTrue(payload["closed"]["projective_hat_conformal_geometry"])
        self.assertTrue(payload["closed"]["plus_sector_source_contract"])
        self.assertFalse(payload["can_solve_omega_now"])
        self.assertTrue(payload["still_open"]["observable_H_hat"])


if __name__ == "__main__":
    unittest.main()
