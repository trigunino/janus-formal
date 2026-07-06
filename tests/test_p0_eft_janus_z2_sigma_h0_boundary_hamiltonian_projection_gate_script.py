import unittest

from scripts.build_p0_eft_janus_z2_sigma_h0_boundary_hamiltonian_projection_gate import (
    build_payload,
)


class H0BoundaryHamiltonianProjectionGateTests(unittest.TestCase):
    def test_h0_requires_lapse_and_constraint_evaluation(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["closure"]["theta_HP_to_ADM_surface_generator_projected"])
        self.assertTrue(payload["closure"]["hamiltonian_constraint_slot_declared"])
        self.assertFalse(payload["closure"]["lapse_time_gauge_normalization_available"])
        self.assertFalse(payload["closure"]["on_shell_constraint_value_available"])
        self.assertFalse(payload["ready_for_background_H0_input"])
        self.assertIn("do_not_read_H0_from_Planck_or_LambdaCDM", payload["forbidden_shortcuts"])
        self.assertIn(
            "derive_active_lapse_time_gauge_normalization_on_Sigma",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
