import unittest

from janus_lab.janus_phase_space_occupation_search import (
    boundary_hilbert_sector_selection_frontier_payload,
)


class JanusBoundaryHilbertSectorSelectionFrontierGateTests(unittest.TestCase):
    def test_required_sector_is_fixed_but_not_selected(self):
        payload = boundary_hilbert_sector_selection_frontier_payload()

        self.assertEqual(payload["required_N"], 1001)
        self.assertEqual(payload["required_CP1_spin_j"], 500.0)
        self.assertEqual(payload["required_KKS_or_CS_level"], 1000)
        self.assertFalse(payload["sector_selection_no_fit_ready"])

    def test_projective_cover_is_not_large_N_selector(self):
        payload = boundary_hilbert_sector_selection_frontier_payload()
        cover = next(row for row in payload["routes"] if row["name"] == "projective_cover_degree")

        self.assertEqual(cover["candidate_N"], 2)
        self.assertFalse(cover["can_reach_required_N"])

    def test_quantum_routes_need_boundary_state_law(self):
        payload = boundary_hilbert_sector_selection_frontier_payload()
        quantum_routes = [
            row for row in payload["routes"] if row["name"] != "projective_cover_degree"
        ]

        self.assertTrue(all(row["can_reach_required_N"] for row in quantum_routes))
        self.assertTrue(
            all(not row["non_circular_selector_available"] for row in quantum_routes)
        )


if __name__ == "__main__":
    unittest.main()
