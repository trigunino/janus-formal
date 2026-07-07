import unittest

from scripts.build_p0_eft_janus_z2_global_bimetric_mass_state_scale_search_gate import (
    build_payload,
)


class GlobalBimetricMassStateScaleSearchGateTests(unittest.TestCase):
    def test_global_routes_are_targets_not_closed_scale(self):
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["any_global_scale_found"])
        self.assertIn(
            "exact_time_dependent_bimetric_solution",
            payload["best_next_routes"],
        )
        self.assertFalse(payload["routes"]["topology_only"]["scale_found"])
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertIn("Noether_Souriau_global_state", payload["routes"])


if __name__ == "__main__":
    unittest.main()
