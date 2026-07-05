import unittest

from scripts.build_p0_eft_janus_z2_sigma_matter_flux_radius_acyclicity_gate import (
    build_payload,
)


class MatterFluxRadiusAcyclicityGateTests(unittest.TestCase):
    def test_perfect_fluid_tangency_is_acyclic_radius_source(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["matter_flux_radius_acyclicity_ledger_declared"])
        self.assertTrue(payload["closure"]["perfect_fluid_tangential_zero_acyclic_ready"])
        self.assertTrue(payload["closure"]["matter_flux_can_enter_radius_solution"])
        self.assertTrue(payload["matter_flux_radius_acyclic_route_ready"])
        self.assertEqual(payload["current_frontier"], [])


if __name__ == "__main__":
    unittest.main()
