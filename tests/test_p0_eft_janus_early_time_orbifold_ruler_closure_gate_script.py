import unittest

from scripts.build_p0_eft_janus_early_time_orbifold_ruler_closure_gate import (
    build_payload,
)


class JanusEarlyTimeOrbifoldRulerClosureGateTests(unittest.TestCase):
    def test_routes_are_structured_and_currently_blocked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["route_count"], 4)
        self.assertFalse(payload["native_early_time_ruler_ready"])
        self.assertEqual(len(payload["closed_route_ids"]), 0)
        self.assertEqual(len(payload["blocked_route_ids"]), 4)
        self.assertTrue(payload["all_routes_pushed_to_current_bottom"])

    def test_late_branch_domain_does_not_reach_drag_marker(self):
        domain = build_payload()["late_branch_domain"]

        self.assertLess(domain["z_max"], domain["fiducial_drag_redshift_marker"])
        self.assertFalse(domain["late_branch_reaches_drag_marker"])
        self.assertLess(domain["q0_required_to_reach_drag_marker"], 0.0)

    def test_projected_plasma_is_ranked_first(self):
        payload = build_payload()

        self.assertEqual(payload["best_next_route"], "projected_photon_baryon_plasma")
        route = next(
            route
            for route in payload["routes"]
            if route["id"] == "projected_photon_baryon_plasma"
        )
        self.assertIn("c_s^J", route["missing_non_rustine_inputs"][0])
        self.assertEqual(route["status"], "blocked_requires_active_plasma_primitives")


if __name__ == "__main__":
    unittest.main()
