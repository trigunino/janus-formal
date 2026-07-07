import unittest

from scripts.build_p0_eft_janus_z2_chi_ll_composite_closure_route_gate import build_payload


class ChiLLCompositeClosureRouteGateTests(unittest.TestCase):
    def test_composite_chain_is_declared_but_not_ready(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertFalse(payload["composite_route_ready"])
        self.assertFalse(payload["chi_LL_prediction_ready"])
        self.assertEqual(payload["first_blocker"], "geometry_area_selector")

    def test_all_expected_chain_steps_exist(self):
        chain = build_payload()["chain"]

        self.assertEqual(
            set(chain),
            {
                "geometry_area_selector",
                "mode_spectrum",
                "source_generation",
                "horizon_energy_check",
                "ll_tension_map",
                "global_charge_interpretation",
            },
        )

    def test_best_next_target_is_upstream_area_selector(self):
        payload = build_payload()

        self.assertEqual(payload["best_next_physical_target"], "geometry_area_selector")
        self.assertIn("functions of R_s", payload["why"])


if __name__ == "__main__":
    unittest.main()
