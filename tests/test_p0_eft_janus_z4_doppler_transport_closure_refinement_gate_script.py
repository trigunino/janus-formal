import unittest

from scripts.build_p0_eft_janus_z4_doppler_transport_closure_refinement_gate import build_payload


class P0EFTJanusZ4DopplerTransportClosureRefinementGateTests(unittest.TestCase):
    def test_refined_doppler_transport_is_strict_and_pre_planck(self):
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-doppler-transport-closure-refinement-gate")
        self.assertTrue(payload["photon_dipole_response_derived"])
        self.assertTrue(payload["baryon_velocity_response_derived"])
        self.assertTrue(payload["Euler_continuity_consistency"])
        self.assertTrue(payload["tight_coupling_consistency"])
        self.assertTrue(payload["gauge_convention_fixed"])
        self.assertTrue(payload["visibility_frozen"])
        self.assertTrue(payload["recombination_frozen"])
        self.assertTrue(payload["no_free_Doppler_amplitude"])
        self.assertTrue(payload["no_direct_Cl_patch"])
        self.assertGreaterEqual(payload["parallel_fraction_Doppler_refined"], 0.0)
        self.assertGreaterEqual(payload["parallel_fraction_full_surface_refined"], 0.0)
        self.assertIn(payload["branch_status"], {
            "strong_z4_surface_candidate",
            "moderate_diagnostic",
            "weak_diagnostic_no_planck",
            "archive_surface_branch",
        })
        self.assertFalse(payload["Planck_trial_allowed"])
        self.assertFalse(payload["diagnostic_surface_trial_allowed"])
        self.assertTrue(payload["no_lambda_retuning"])
        self.assertTrue(payload["no_free_slip_parameter"])
        self.assertTrue(payload["no_free_eta_ratio"])
        self.assertTrue(payload["raw_toy_LOS_forbidden"])
        self.assertFalse(payload["profiled_planck_candidate"])
        self.assertFalse(payload["full_planck_validation"])


if __name__ == "__main__":
    unittest.main()
