import unittest

from janus_lab.janus_phase_space_occupation_search import (
    early_universe_native_plasma_frontier_verdict_payload,
)


class JanusEarlyUniverseNativePlasmaFrontierVerdictGateTests(unittest.TestCase):
    def test_frontier_keeps_bao_prediction_blocked(self):
        payload = early_universe_native_plasma_frontier_verdict_payload()

        self.assertIn("numeric z_d^J and r_d^J", payload["blocked"])
        self.assertIn("import Lambda-CDM r_d", payload["not_allowed"])

    def test_surviving_routes_include_boundary_state_law(self):
        payload = early_universe_native_plasma_frontier_verdict_payload()
        routes = [row["route"] for row in payload["surviving_routes"]]

        self.assertEqual(
            routes,
            [
                "derive_high_power_photon_clock_transport",
                "derive_attached_early_branch",
                "derive_boundary_state_law_for_N",
            ],
        )


if __name__ == "__main__":
    unittest.main()
