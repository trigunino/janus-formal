import unittest

from scripts.run_p0_eft_janus_z4_official_planck_acoustic_driving_delta_trial import (
    COMPONENTS,
    LAMBDAS,
    build_payload,
)


class P0EFTJanusZ4OfficialPlanckAcousticDrivingDeltaTrialTests(unittest.TestCase):
    def test_trial_scaffold_without_official_likelihood(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "official-planck-acoustic-driving-delta-trial")
        self.assertFalse(payload["is_planck_success_verdict"])
        self.assertTrue(payload["not_full_z4_verdict"])
        self.assertEqual(payload["trial_type"], "effective_acoustic_temperature_source_delta")
        self.assertEqual(payload["backend"], "camb_gr_plus_z4_delta")
        self.assertTrue(payload["acoustic_gate_passed"])
        self.assertEqual(payload["delta_channels_enabled"], ["acoustic_temperature_source"])
        self.assertEqual(tuple(payload["component_trials"]), COMPONENTS)
        self.assertEqual(tuple(payload["lambda_grid"]), LAMBDAS)
        self.assertTrue(payload["metric_split_used"])
        self.assertEqual(payload["deltaSlip_Z4"], "explicit_zero_until_derived")
        self.assertFalse(payload["polarization_source_delta_enabled"])
        self.assertTrue(payload["EE_expected_unchanged"])
        self.assertFalse(payload["lensing_delta_enabled"])
        self.assertTrue(payload["C_phi_phi_expected_unchanged"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["visibility_delta_enabled"])
        self.assertFalse(payload["background_projection_changed"])
        self.assertFalse(payload["primordial_delta_enabled"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["full_native_z4_solver_used"])
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        for component in COMPONENTS:
            diagnostics = payload["components"][component]["diagnostics"]
            self.assertEqual(diagnostics["0.0"]["EE_max_delta"], 0.0)
            self.assertEqual(diagnostics["0.0"]["Cphiphi_max_delta"], 0.0)
            self.assertEqual(diagnostics["0.0"]["max_abs_transfer_response"], 0.0)
            self.assertIn("spectra_paths", payload["components"][component])


if __name__ == "__main__":
    unittest.main()
