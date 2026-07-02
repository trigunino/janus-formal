import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_surface_doppler_decomposition_gate import build_payload


class P0EFTJanusZ4DerivedSlipSurfaceDopplerDecompositionGateTests(unittest.TestCase):
    def test_doppler_decomposition_reports_sw_and_doppler_channels(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-surface-doppler-decomposition-gate")
        self.assertLess(payload["parallel_fraction_SW_only"], 0.50)
        self.assertGreaterEqual(payload["parallel_fraction_Doppler_only"], 0.0)
        self.assertGreaterEqual(payload["parallel_fraction_full_surface"], payload["parallel_fraction_SW_only"])
        self.assertTrue(payload["doppler_reintroduces_carrier_tangency"])
        self.assertTrue(payload["SW_surface_promising"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["candidate_promotion_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_doppler_amplitude"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
