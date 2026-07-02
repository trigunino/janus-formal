import unittest

from scripts.run_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial import (
    LAMBDA_E_GRID,
    LAMBDA_T_GRID,
    build_payload,
)


class P0EFTJanusZ4OfficialPlanckClosedBoltzmannAcousticPolarizationTrialTests(unittest.TestCase):
    def test_closed_boltzmann_trial_scaffold(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "official-planck-closed-boltzmann-acoustic-polarization-trial")
        self.assertEqual(payload["trial_type"], "closed_boltzmann_effective_acoustic_polarization_trial")
        self.assertTrue(payload["not_full_planck_verdict"])
        self.assertTrue(payload["not_full_native_z4_solver"])
        self.assertEqual(payload["lambda_T_grid"], list(LAMBDA_T_GRID))
        self.assertEqual(payload["lambda_E_grid"], list(LAMBDA_E_GRID))
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertTrue(payload["lensing_C_phi_phi_frozen"])
        self.assertTrue(payload["slip_frozen"])
        self.assertTrue(payload["Pi_source_from_multipoles"])
        self.assertFalse(payload["free_Theta2_source_tag"])
        self.assertTrue(payload["available_planck_channels_only"])
        self.assertFalse(payload["standalone_highl_TE_EE_available"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertFalse(payload["full_planck_verdict"])
        self.assertEqual(len(payload["trial_rows"]), len(LAMBDA_T_GRID) * len(LAMBDA_E_GRID))


if __name__ == "__main__":
    unittest.main()
