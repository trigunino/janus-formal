import unittest

from scripts.build_p0_eft_janus_z4_derived_slip_photon_monopole_sw_closure_gate import build_payload


class P0EFTJanusZ4DerivedSlipPhotonMonopoleSWClosureGateTests(unittest.TestCase):
    def test_photon_monopole_sw_closure_is_derived_and_keeps_planck_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-derived-slip-photon-monopole-sw-closure-gate")
        self.assertTrue(payload["deltaPsi_Z4_from_derived_slip"])
        self.assertTrue(payload["deltaPhi_Z4_from_derived_slip"])
        self.assertTrue(payload["photon_monopole_response_declared"])
        self.assertFalse(payload["deltaTheta0_Z4_free"])
        self.assertTrue(payload["doppler_response_declared"])
        self.assertFalse(payload["Doppler_Z4_free"])
        self.assertIn("deltaTheta0_Z4", payload["surface_SW_source"])
        self.assertIn("Doppler_Z4", payload["full_surface_source"])
        self.assertTrue(payload["gauge_convention_declared"])
        self.assertTrue(payload["visibility_frozen"])
        self.assertTrue(payload["recombination_frozen"])
        self.assertTrue(payload["tight_coupling_policy_declared"])
        self.assertGreaterEqual(payload["potential_only_parallel_fraction"], 0.0)
        self.assertGreaterEqual(payload["monopole_plus_potential_parallel_fraction"], 0.0)
        self.assertGreaterEqual(payload["full_surface_parallel_fraction"], 0.0)
        self.assertIn("full_surface", payload["subchannel_projection"])
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
