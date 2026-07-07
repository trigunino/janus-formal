import unittest

from scripts.build_p0_eft_janus_z2_published_bimetric_flrw_sector_source_reduction_gate import (
    build_payload,
)


class PublishedBimetricFLRWSectorSourceReductionGateTests(unittest.TestCase):
    def test_dust_shape_is_ready_but_normalization_is_not(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["shape_level"]["rho_p_shape_ready"])
        self.assertFalse(payload["rho_p_normalized_ready"])
        self.assertEqual(payload["primary_blocker"], "plus_minus_density_normalizations")
        self.assertTrue(payload["normalization_level"]["global_bimetric_equations_available"])
        self.assertFalse(payload["normalization_level"]["global_stress_energy_mass_available"])
        self.assertFalse(payload["normalization_level"]["sector_normalizations_ready"])
        self.assertEqual(
            payload["upstream_sector_normalization"]["primary_blocker"],
            "missing_global_bimetric_stress_energy_state_inputs",
        )

    def test_forbids_observational_density_shortcuts(self):
        payload = build_payload()

        forbidden = payload["normalization_level"]["forbidden_sources"]
        self.assertIn("observational fit", forbidden)
        self.assertIn("reuse LCDM omega_b/omega_cdm", forbidden)
        self.assertIn("reuse N_gap as density without projection map", forbidden)


if __name__ == "__main__":
    unittest.main()
