import unittest

from scripts.build_p0_eft_janus_z2_sigma_growth_prediction_vector_gate import build_payload


class P0EFTJanusZ2SigmaGrowthPredictionVectorGateTests(unittest.TestCase):
    def test_gate_blocks_until_numeric_closure_exists(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["bibliography_checked"])
        self.assertTrue(payload["closure"]["growth_perturbation_equations_derived"])
        self.assertFalse(payload["closure"]["numerical_background_closure_ready"])
        self.assertFalse(payload["closure"]["numerical_H_Z2Sigma_ready"])
        self.assertFalse(payload["closure"]["numerical_mu_Z2Sigma_ready"])
        self.assertFalse(payload["growth_prediction_vector_prerequisites_ready"])
        self.assertFalse(payload["z2_sigma_growth_prediction_vector_ready"])

    def test_archived_growth_solvers_are_forbidden(self):
        payload = build_payload()

        self.assertIn("scripts.run_p0_eft_holst_membrane_co_optimisation.branch_curve", payload["forbidden_reuse"])
        self.assertIn("archived_z4_mu_sigma_tables", payload["forbidden_reuse"])
        self.assertIn("export_fsigma8_prediction_vector_at_sdss_eboss_redshifts", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
