import unittest

from scripts.build_p0_eft_janus_z2_sigma_h0_surface_energy_normalization_frontier_gate import (
    build_payload,
)


class H0SurfaceEnergyNormalizationFrontierGateTests(unittest.TestCase):
    def test_h0_is_blocked_by_surface_energy_not_lapse(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["frontier"], "boundary_surface_energy_normalization")
        self.assertTrue(payload["closure"]["branch_lapse_convention_fixed_for_FLRW"])
        self.assertTrue(payload["closure"]["boundary_reference_zero_point_fixed"])
        self.assertTrue(payload["closure"]["brown_york_charge_formula_reduced"])
        self.assertFalse(payload["closure"]["brown_york_charge_inputs_complete"])
        self.assertFalse(payload["closure"]["on_shell_Hamiltonian_constraint_value_available"])
        self.assertFalse(
            payload["closure"]["Z2Sigma_boundary_surface_energy_normalization_available"]
        )
        self.assertFalse(payload["ready_for_background_H0_input"])
        self.assertIn(
            "do_not_promote_N_equals_1_to_numeric_H0",
            payload["forbidden_shortcuts"],
        )
        self.assertIn(
            "derive_k_ref_minus_k_phys_on_active_Z2Sigma_time_leaf",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
