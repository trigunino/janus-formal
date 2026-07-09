import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    alpha_non_full_investigated_routes_payload,
)


class JanusAlphaNonFullInvestigatedRoutesFrontierGateTests(unittest.TestCase):
    def test_all_non_full_routes_are_pushed_but_not_closed(self):
        payload = alpha_non_full_investigated_routes_payload()
        self.assertFalse(payload["any_route_closes_alpha_now"])
        self.assertEqual(payload["routes_pushed_count"], 8)

    def test_each_route_has_frontier_and_blockers(self):
        payload = alpha_non_full_investigated_routes_payload()
        for route in payload["routes"]:
            self.assertGreaterEqual(len(route["what_closes"]), 2)
            self.assertGreaterEqual(len(route["what_still_blocks"]), 4)
            self.assertTrue(route["frontier_verdict"])

    def test_priority_order_keeps_unimodular_first(self):
        payload = alpha_non_full_investigated_routes_payload()
        self.assertEqual(payload["best_remaining_order"][0], "unimodular_four_form_sector")


if __name__ == "__main__":
    unittest.main()
