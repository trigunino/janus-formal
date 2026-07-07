import unittest

from scripts.build_p0_eft_janus_z2_sigma_noether_hamiltonian_boundary_charge_gate import (
    build_payload,
)


class NoetherHamiltonianBoundaryChargeGateTests(unittest.TestCase):
    def test_noether_charge_kind_is_fixed_but_numeric_value_is_not(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["charge_kind"], "Hamiltonian_boundary_energy")
        self.assertTrue(payload["symbolic_boundary_hamiltonian_ready"])
        self.assertFalse(payload["numeric_boundary_hamiltonian_ready"])
        self.assertTrue(payload["closure"]["dimensionless_lapse_available"])
        self.assertTrue(payload["closure"]["symbolic_surface_measure_available"])
        self.assertFalse(payload["closure"]["physical_lapse_normalization_available"])
        self.assertFalse(payload["closure"]["absolute_surface_measure_available"])
        self.assertIn("boundary_charge_value_available", payload["blocked_by"])
        self.assertIn("absolute_surface_measure_available", payload["blocked_by"])
        self.assertIn("delta H_xi", payload["covariant_phase_space_formula"])


if __name__ == "__main__":
    unittest.main()
