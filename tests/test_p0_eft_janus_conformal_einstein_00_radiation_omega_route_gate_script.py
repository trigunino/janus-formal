import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    conformal_einstein_00_radiation_omega_route_payload,
)


class JanusConformalEinstein00RadiationOmegaRouteGateTests(unittest.TestCase):
    def test_00_projection_includes_radiation_but_solution_open(self):
        payload = conformal_einstein_00_radiation_omega_route_payload()
        self.assertTrue(payload["projection_choice_closed"])
        self.assertFalse(payload["omega_solution_closed"])
        self.assertTrue(payload["checks"]["radiation_source_visible_in_00"])


if __name__ == "__main__":
    unittest.main()
