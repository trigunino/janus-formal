import unittest

from src.janus_lab.janus_phase_space_occupation_search import omega_internal_route_exhaustion_matrix_payload


class JanusOmegaInternalRouteExhaustionMatrixGateTests(unittest.TestCase):
    def test_no_internal_route_closed(self):
        payload = omega_internal_route_exhaustion_matrix_payload()
        self.assertFalse(payload["any_internal_route_closed"])
        self.assertGreaterEqual(len(payload["routes"]), 8)


if __name__ == "__main__":
    unittest.main()
