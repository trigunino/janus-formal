import unittest

from scripts.run_p0_eft_janus_z4_official_planck_lensing_shape_delta_trial import LAMBDAS, build_payload


class P0EFTJanusZ4OfficialPlanckLensingShapeDeltaTrialTests(unittest.TestCase):
    def test_trial_scaffold_without_official_likelihood(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "official-planck-lensing-shape-delta-trial")
        self.assertFalse(payload["is_planck_success_verdict"])
        self.assertTrue(payload["eligibility_gate_passed"])
        self.assertEqual(payload["backend"], "camb_gr_plus_z4_delta")
        self.assertEqual(payload["delta_channels_enabled"], ["weyl_lensing_shape"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["full_native_z4_solver_used"])
        self.assertEqual(tuple(payload["lambda_grid"]), LAMBDAS)
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertEqual(payload["trial_rows"], {})
        for lam in LAMBDAS:
            self.assertIn(str(lam), payload["spectra_paths"])
            self.assertIn(str(lam), payload["band_response"])


if __name__ == "__main__":
    unittest.main()
