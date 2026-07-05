import unittest

from scripts.build_p0_eft_janus_z2_sigma_early_plasma_normalization_builder_gate import build_payload


class P0EFTJanusZ2SigmaEarlyPlasmaNormalizationBuilderGateTests(unittest.TestCase):
    def test_normalization_builder_forbids_planck_defaults(self):
        payload = build_payload()

        self.assertTrue(payload["baryon_number_density_builder_ready"])
        self.assertTrue(payload["baryon_mass_density_from_number_builder_ready"])
        self.assertTrue(payload["conserved_photon_temperature_builder_ready"])
        self.assertTrue(payload["blackbody_photon_density_builder_ready"])
        self.assertTrue(payload["requires_active_photon_temperature_normalization"])
        self.assertTrue(payload["requires_active_photon_temperature"])
        self.assertTrue(payload["requires_active_baryon_mass_density"])
        self.assertTrue(payload["requires_active_baryon_number_density"])
        self.assertTrue(payload["requires_active_ionization_fraction"])
        self.assertFalse(payload["uses_planck_Tcmb_default"])
        self.assertFalse(payload["uses_planck_omega_b_default"])
        self.assertFalse(payload["uses_planck_lcdm_recombination_history"])
        self.assertFalse(payload["uses_archived_z4_inputs"])
        self.assertFalse(payload["early_plasma_normalization_values_ready"])


if __name__ == "__main__":
    unittest.main()
