import unittest

from scripts.run_p0_eft_janus_z4_official_planck_weyl_late_isw_delta_trial import LAMBDAS, build_payload


class P0EFTJanusZ4OfficialPlanckWeylLateISWDeltaTrialTests(unittest.TestCase):
    def test_trial_scaffold_without_official_likelihood(self):
        payload = build_payload(run_official=False)

        self.assertEqual(payload["status"], "official-planck-weyl-late-isw-delta-trial")
        self.assertFalse(payload["is_planck_success_verdict"])
        self.assertTrue(payload["consistency_gate_passed"])
        self.assertEqual(payload["backend"], "camb_gr_plus_z4_delta")
        self.assertEqual(payload["delta_channels_enabled"], ["shared_weyl_lensing", "late_isw_source"])
        self.assertFalse(payload["early_isw_enabled"])
        self.assertFalse(payload["acoustic_delta_enabled"])
        self.assertFalse(payload["recombination_delta_enabled"])
        self.assertFalse(payload["polarization_delta_enabled"])
        self.assertFalse(payload["native_toy_los_used"])
        self.assertFalse(payload["full_native_z4_solver_used"])
        self.assertEqual(payload["trial_type"], "effective_shared_weyl_late_isw")
        self.assertEqual(tuple(payload["lambda_grid"]), LAMBDAS)
        self.assertFalse(payload["official_likelihood_requested"])
        self.assertFalse(payload["official_likelihood_executed"])
        self.assertTrue(payload["response_stats"]["TE_EE_frozen_by_construction"])


if __name__ == "__main__":
    unittest.main()
