import unittest

from src.janus_lab.janus_phase_space_occupation_search import alpha_three_frontier_laws_payload


class JanusAlphaThreeFrontierLawsGateTests(unittest.TestCase):
    def test_three_frontiers_are_documented_and_not_closed(self):
        payload = alpha_three_frontier_laws_payload()
        self.assertFalse(payload["any_route_closed_now"])
        self.assertEqual(len(payload["routes"]), 3)
        self.assertEqual(
            [route["name"] for route in payload["routes"]],
            [
                "unimodular_four_form_sector",
                "weyl_conformal_anomaly_state_law",
                "euclidean_s4_rp4_no_boundary_saddle",
            ],
        )

    def test_every_route_has_a_hard_blocker(self):
        payload = alpha_three_frontier_laws_payload()
        for route in payload["routes"]:
            self.assertGreaterEqual(len(route["missing_inputs"]), 4)
            self.assertFalse(route["no_fit_alpha_generated"])


if __name__ == "__main__":
    unittest.main()
