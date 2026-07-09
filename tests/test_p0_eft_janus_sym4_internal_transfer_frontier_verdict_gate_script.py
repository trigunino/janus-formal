import unittest

from janus_lab.janus_phase_space_occupation_search import (
    sym4_internal_transfer_frontier_verdict_payload,
)


class JanusSym4InternalTransferFrontierVerdictGateTests(unittest.TestCase):
    def test_exhausted_routes_are_recorded(self):
        payload = sym4_internal_transfer_frontier_verdict_payload()

        self.assertEqual(payload["target"]["Hilbert_dimension"], 1001)
        self.assertGreaterEqual(len(payload["exhausted_routes"]), 5)
        self.assertIn("manual basis ordering: rejected as rustine", payload["exhausted_routes"])

    def test_next_route_is_action_or_modular_not_combinatorics(self):
        payload = sym4_internal_transfer_frontier_verdict_payload()

        self.assertEqual(payload["current_best_non_rustine_route"], "non_diagonal_PT_Sigma_boundary_action_H_normal")
        self.assertIn("do not add more combinatorial selectors", payload["stop_condition_for_this_subbranch"])
        self.assertFalse(payload["no_fit_closed_now"])


if __name__ == "__main__":
    unittest.main()
