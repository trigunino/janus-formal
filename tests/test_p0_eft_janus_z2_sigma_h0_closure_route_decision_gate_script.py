import unittest

from scripts.build_p0_eft_janus_z2_sigma_h0_closure_route_decision_gate import (
    build_payload,
)


class H0ClosureRouteDecisionGateTests(unittest.TestCase):
    def test_reference_route_does_not_directly_promote_energy_to_h0(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(
            payload["selected_next_route"],
            "B_quasilocal_reference_plus_Hamiltonian_to_Friedmann_map",
        )
        route_b = payload["routes"]["B_quasilocal_reference"]
        self.assertTrue(route_b["zero_reference_fixed"])
        self.assertFalse(route_b["direct_H0_formula_dimensionally_valid"])
        self.assertTrue(payload["hamiltonian_to_friedmann_map_symbolic_ready"])
        self.assertFalse(payload["hamiltonian_to_friedmann_map_numeric_ready"])
        self.assertFalse(payload["h0_numeric_inputs_available"])
        self.assertFalse(payload["can_provide_absolute_RSigma"])
        self.assertFalse(payload["can_provide_state_charge"])
        self.assertFalse(payload["can_provide_action_scale"])
        self.assertFalse(payload["H0_Z2Sigma_closure_ready"])
        self.assertIn(
            "do_not_identify_energy_dimension_with_H0_dimension",
            payload["forbidden_shortcuts"],
        )


if __name__ == "__main__":
    unittest.main()
