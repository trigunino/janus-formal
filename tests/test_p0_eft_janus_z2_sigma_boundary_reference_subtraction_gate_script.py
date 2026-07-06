import unittest

from scripts.build_p0_eft_janus_z2_sigma_boundary_reference_subtraction_gate import (
    build_payload,
)


class BoundaryReferenceSubtractionGateTests(unittest.TestCase):
    def test_reference_subtraction_fixes_zero_not_h0_value(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["zero_point_fixed"])
        self.assertFalse(payload["new_sigma_density_introduced"])
        self.assertTrue(payload["closure"]["Hamiltonian_value_carried_by_boundary_term"])
        self.assertTrue(payload["closure"]["reference_vacuum_zero_energy_condition_declared"])
        self.assertFalse(payload["closure"]["physical_boundary_charge_magnitude_available"])
        self.assertFalse(payload["ready_for_H0_normalization"])
        self.assertIn("do_not_set_H0_from_reference_zero_condition_alone", payload["forbidden_shortcuts"])


if __name__ == "__main__":
    unittest.main()
