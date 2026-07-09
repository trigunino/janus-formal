import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    alpha_combination_frontier_matrix_payload,
)


class JanusAlphaCombinationFrontierMatrixGateTests(unittest.TestCase):
    def test_combination_matrix_terminal_verdict(self):
        payload = alpha_combination_frontier_matrix_payload()
        self.assertEqual(payload["combination_count"], 9)
        self.assertFalse(payload["any_no_fit_combination_closes_now"])
        self.assertTrue(payload["calibrated_sector_can_close"])

    def test_best_routes_are_named(self):
        payload = alpha_combination_frontier_matrix_payload()
        self.assertEqual(payload["best_no_fit_candidate"], "flux_pt_selector")
        self.assertEqual(payload["best_non_throat_candidate"], "weyl_anomaly_topological_vacuum")
        self.assertEqual(payload["best_janus_matter_candidate"], "janus_matter_global_energy")

    def test_every_combination_has_conditions(self):
        payload = alpha_combination_frontier_matrix_payload()
        for combo in payload["combinations"]:
            self.assertGreaterEqual(len(combo["components"]), 2)
            self.assertGreaterEqual(len(combo["could_close_if"]), 2)
            self.assertTrue(combo["terminal_assessment"])


if __name__ == "__main__":
    unittest.main()
