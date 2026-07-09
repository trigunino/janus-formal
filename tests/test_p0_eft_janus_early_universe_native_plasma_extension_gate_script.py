import unittest

from janus_lab.janus_early_universe_native_plasma import (
    VariableConstantGauge,
    candidate_plasma_scaling_laws,
    native_plasma_extension_contract,
)
from scripts.build_p0_eft_janus_early_universe_native_plasma_extension_gate import (
    build_payload,
)


class JanusEarlyUniverseNativePlasmaExtensionGateTests(unittest.TestCase):
    def test_eq40_closes_local_microphysics_scalings(self):
        scalings = VariableConstantGauge.janus_2026_eq40().microphysics_scalings()

        self.assertEqual(scalings["alpha_fs"], 0.0)
        self.assertEqual(scalings["rest_energy"], 0.0)
        self.assertEqual(scalings["hydrogen_ionization_energy"], 0.0)
        self.assertEqual(scalings["compton_length"], 1.0)
        self.assertEqual(scalings["sigma_thomson_area"], 2.0)

    def test_contract_does_not_fake_density_or_hubble_closure(self):
        contract = native_plasma_extension_contract()

        self.assertIn(
            "active baryon number charge N_b^J or equivalent density normalization",
            contract["model_must_add_or_derive"],
        )
        self.assertIn(
            "pre-drag two-sector H_J(a) from bimetric equations",
            contract["model_must_add_or_derive"],
        )

    def test_candidate_scaling_laws_expose_drag_epoch_obstruction(self):
        candidates = {candidate.name: candidate for candidate in candidate_plasma_scaling_laws()}

        eq40 = candidates["eq40_comoving_photon_energy"]
        self.assertEqual(eq40.rho_gamma_exponent, -3.0)
        self.assertEqual(eq40.rho_baryon_energy_exponent, -3.0)
        self.assertEqual(eq40.blackbody_photon_number_density_exponent, -3.0)
        self.assertTrue(eq40.blackbody_matches_conserved_photon_number)
        self.assertEqual(eq40.gamma_over_h_exponent_before_ionization, 0.0)
        self.assertEqual(
            eq40.verdict(),
            "drag_epoch_not_selected_without_extra_ionization_entropy_law",
        )

        thermal = candidates["thermodynamic_cooling_photon_energy"]
        self.assertEqual(thermal.rho_gamma_exponent, -4.0)
        self.assertEqual(thermal.baryon_loading_exponent, 1.0)
        self.assertEqual(thermal.blackbody_photon_number_density_exponent, -6.0)
        self.assertFalse(thermal.blackbody_matches_conserved_photon_number)
        self.assertEqual(
            thermal.verdict(),
            "requires_photon_entropy_or_phase_space_production_law",
        )

        compensated = candidates["phase_space_compensated_thermal_cooling"]
        self.assertEqual(compensated.phase_space_occupation_exponent, 3.0)
        self.assertEqual(compensated.blackbody_photon_number_density_exponent, -3.0)
        self.assertTrue(compensated.blackbody_matches_conserved_photon_number)
        self.assertEqual(
            compensated.verdict(),
            "can_select_drag_epoch_if_temperature_law_is_derived",
        )

    def test_gate_structures_extension_without_evaluating_rd(self):
        payload = build_payload()

        self.assertTrue(payload["extension_structured"])
        self.assertTrue(payload["eq40_microphysics_partially_closed"])
        self.assertFalse(payload["native_rd_evaluated"])
        self.assertFalse(payload["native_bao_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
