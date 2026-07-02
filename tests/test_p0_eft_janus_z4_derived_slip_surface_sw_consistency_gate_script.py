import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_surface_sw_consistency_gate import build_payload


class P0EFTJanusZ4DerivedSlipSurfaceSWConsistencyGateTests(unittest.TestCase):
    def test_surface_sw_consistency_blocks_without_photon_monopole(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-surface-sw-consistency-gate")
        self.assertTrue(payload["surface_term_parallel_fraction_recorded"])
        self.assertTrue(payload["full_derived_slip_archived"])
        self.assertTrue(payload["deltaPsi_Z4_derived_from_slip"])
        self.assertFalse(payload["delta_gamma_Z4_photon_monopole_response_declared"])
        self.assertFalse(payload["SW_combination_consistency_checked"])
        self.assertFalse(payload["Doppler_leakage_checked"])
        self.assertTrue(payload["gauge_convention_declared"])
        self.assertTrue(payload["visibility_unchanged"])
        self.assertTrue(payload["recombination_unchanged"])
        self.assertFalse(payload["surface_SW_physical_closure"])
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["diagnostic_surface_only_trial_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
