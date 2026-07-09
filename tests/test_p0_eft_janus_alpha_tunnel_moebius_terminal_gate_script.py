import unittest

from src.janus_lab.janus_phase_space_occupation_search import (
    alpha_tunnel_moebius_routes_terminal_payload,
)


class JanusAlphaTunnelMoebiusTerminalGateTests(unittest.TestCase):
    def test_partial_routes_are_now_terminally_audited(self):
        payload = alpha_tunnel_moebius_routes_terminal_payload()
        self.assertTrue(payload["all_investigated_to_end"])
        self.assertFalse(payload["any_route_closes_alpha_now"])
        self.assertEqual(payload["routes_pushed_count"], 2)

    def test_routes_are_topology_only_without_alpha_selector(self):
        payload = alpha_tunnel_moebius_routes_terminal_payload()
        for route in payload["routes"]:
            self.assertGreaterEqual(len(route["what_it_provides"]), 3)
            self.assertGreaterEqual(len(route["what_it_does_not_provide"]), 4)
            self.assertTrue(route["terminal_verdict"])


if __name__ == "__main__":
    unittest.main()
