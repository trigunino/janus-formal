import unittest

from scripts.run_p0_eft_janus_z4_official_planck_polarization_source_delta_trial import (
    LAMBDA_E_GRID,
    SUBCHANNELS,
    build_payload,
)


class P0EFTJanusZ4OfficialPlanckPolarizationSourceDeltaTrialTests(unittest.TestCase):
    def test_trial_scaffold_without_official_likelihood(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "official-planck-polarization-source-delta-trial")
        self.assertEqual(payload["trial_type"], "effective_polarization_source_delta_trial")
        self.assertTrue(payload["not_full_planck_verdict"])
        self.assertTrue(payload["not_full_native_z4_solver"])
        self.assertEqual(payload["theta2_pi_derivation_status"], "source_tagged_effective")
        self.assertTrue(payload["temperature_channel_fixed"])
        self.assertEqual(payload["lambda_T_fixed"], -0.008)
        self.assertTrue(payload["lambda_E_scanned"])
        self.assertEqual(tuple(payload["lambda_E_grid"]), LAMBDA_E_GRID)
        self.assertEqual(tuple(payload["subchannels"]), SUBCHANNELS)
        self.assertFalse(payload["direct_Cl_patch"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["r_s_changed"])
        self.assertFalse(payload["r_d_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertFalse(payload["lensing_delta_enabled"])
        self.assertTrue(payload["C_phi_phi_unchanged"])
        self.assertTrue(payload["available_planck_channels_only"])
        self.assertTrue(payload["missing_highl_TE_EE_standalone_clik"])
        self.assertEqual(payload["lensing_likelihood_shift_source"], "primary_CMB_spectra")
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        for result in payload["subchannel_results"].values():
            self.assertIn("spectra_paths", result)
            self.assertEqual(len(result["spectra_paths"]), len(LAMBDA_E_GRID))
            self.assertEqual(result["diagnostics"]["0.0"]["TT_delta_when_lambda_E_changes"], 0.0)
            self.assertEqual(result["diagnostics"]["0.0"]["Cphiphi_delta_when_lambda_E_changes"], 0.0)


if __name__ == "__main__":
    unittest.main()
