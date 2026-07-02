import unittest

from scripts.build_p0_eft_janus_z4_two_sector_initial_mode_gate import build_payload


class P0EFTJanusZ4TwoSectorInitialModeGateTests(unittest.TestCase):
    def test_two_sector_initial_modes_are_independent_and_pre_spectra(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-two-sector-initial-mode-gate")
        self.assertTrue(payload["conservation_bianchi_gate_passed"])
        self.assertTrue(payload["mode_basis_declared"])
        self.assertGreaterEqual(payload["mode_basis_rank"], 5)
        self.assertTrue(payload["mode_independence_passed"])
        self.assertTrue(payload["plus_adiabatic_mode_declared"])
        self.assertTrue(payload["minus_adiabatic_mode_declared"])
        self.assertTrue(payload["symmetric_two_sector_mode_declared"])
        self.assertTrue(payload["antisymmetric_Z4_mode_declared"])
        self.assertTrue(payload["relative_isocurvature_mode_declared"])
        self.assertTrue(payload["projection_mode_declared"])
        self.assertTrue(payload["superhorizon_regular"])
        self.assertTrue(payload["constraint_compatible_modes"])
        self.assertTrue(payload["Bianchi_compatible_initial_conditions"])
        self.assertTrue(payload["projection_consistent_initial_conditions"])
        self.assertTrue(payload["GR_limit_plus_mode_matches_standard"])
        self.assertTrue(payload["minus_sector_mode_not_collapsed_into_rho_eff"])
        self.assertTrue(payload["standard_CAMB_adiabatic_forcing_forbidden"])
        self.assertFalse(payload["single_sector_adiabatic_only"])
        self.assertFalse(payload["rho_eff_initial_condition"])
        self.assertFalse(payload["hidden_sector_forced_to_plus_sector"])
        self.assertFalse(payload["arbitrary_relative_isocurvature_amplitude"])
        self.assertFalse(payload["spectra_generation_allowed"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
