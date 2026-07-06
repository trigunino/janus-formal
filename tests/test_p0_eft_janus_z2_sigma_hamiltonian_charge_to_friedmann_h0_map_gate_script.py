import unittest

from scripts.build_p0_eft_janus_z2_sigma_hamiltonian_charge_to_friedmann_h0_map_gate import (
    build_payload,
)


class HamiltonianChargeToFriedmannH0MapGateTests(unittest.TestCase):
    def test_symbolic_map_is_ready_but_numeric_h0_waits_for_charge_volume_curvature(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["symbolic_map_ready"])
        self.assertFalse(payload["numeric_H0_ready"])
        self.assertIn("boundary_charge_value_available", payload["blocked_by"])
        self.assertIn("effective_volume_value_available", payload["blocked_by"])
        self.assertIn("curvature_radius_value_available", payload["blocked_by"])
        self.assertIn("H0_SI^2", payload["map"]["friedmann_at_a1"])


if __name__ == "__main__":
    unittest.main()
