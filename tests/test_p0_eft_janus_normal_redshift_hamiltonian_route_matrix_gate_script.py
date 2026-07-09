import unittest

from janus_lab.janus_phase_space_occupation_search import (
    normal_redshift_hamiltonian_route_matrix_payload,
)


class JanusNormalRedshiftHamiltonianRouteMatrixGateTests(unittest.TestCase):
    def test_recommends_boundary_action_hamiltonian(self):
        payload = normal_redshift_hamiltonian_route_matrix_payload()

        self.assertEqual(payload["recommended_next_route"], "PT_Sigma_boundary_action_H")
        self.assertIn("PT_Sigma_boundary_action_H", payload["viable_non_rustine_routes"])
        self.assertIn("boundary_modular_H", payload["viable_non_rustine_routes"])

    def test_rejects_manual_ordering_and_keeps_not_closed(self):
        payload = normal_redshift_hamiltonian_route_matrix_payload()
        rows = {row["name"]: row for row in payload["routes"]}

        self.assertFalse(rows["empirical_or_lexicographic_ordering"]["non_rustine"])
        self.assertFalse(payload["no_fit_closed_now"])
        self.assertEqual(payload["if_recommended_route_closes"]["z_max"], 1000.0)


if __name__ == "__main__":
    unittest.main()
