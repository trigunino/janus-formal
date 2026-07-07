import unittest

from scripts.build_p0_eft_janus_z2_cosmological_charge_projection_exhaustion_gate import (
    build_payload,
)


class CosmologicalChargeProjectionExhaustionGateTests(unittest.TestCase):
    def test_route_is_plausible_but_exhausted_without_state(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["current_no_extension_projection_route_exhausted"])
        self.assertEqual(
            payload["intuition_status"],
            "physically_plausible_but_requires_state_or_projection_theorem",
        )

    def test_minimal_missing_theorems_are_explicit(self):
        missing = build_payload()["minimal_missing_theorems"]

        self.assertIn("absolute_N_occ_or_global_mass_state_selection", missing)
        self.assertIn("active_spatial_volume_or_quasilocal_surface_measure", missing)
        self.assertIn("Sigma_PT_projection_completeness", missing)
        self.assertIn("Q_Sigma_equals_M_bridge_c2", missing)

    def test_channel_distinction_is_kept(self):
        channels = build_payload()["channels"]

        self.assertFalse(channels["baryon_number_or_occupation"]["absolute_value_selected"])
        self.assertEqual(
            channels["stress_energy_total_mass"]["conserved"],
            "definition_dependent",
        )
        self.assertEqual(
            channels["bridge_quasilocal_mass"]["conserved"],
            "if_Q_Sigma_equals_M_bridge_c2_is_proved",
        )


if __name__ == "__main__":
    unittest.main()
