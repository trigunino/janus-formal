import unittest

from scripts.build_p0_eft_janus_z2_sigma_bao_scale_free_formulation_gate import build_payload


class P0EFTJanusZ2SigmaBAOScaleFreeFormulationGateTests(unittest.TestCase):
    def test_scale_free_formulation_matches_dimensional_bao_ratios(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["dimensional_equivalence_test_passed"])
        self.assertTrue(payload["dimensionless_E_builder_ready"])
        self.assertTrue(payload["dimensionless_drag_ratio_builder_ready"])
        self.assertTrue(payload["scale_free_zd_solver_ready"])
        self.assertLess(payload["max_abs_prediction_delta"], 1.0e-9)
        self.assertTrue(payload["bao_ratios_depend_on_H0_only_through_self_consistent_rd_hat"])
        self.assertFalse(payload["observational_H0_fit_used"])
        self.assertFalse(payload["compressed_planck_lcdm_rd_used"])
        self.assertFalse(payload["archived_z4_reuse_used"])
        self.assertFalse(payload["official_bao_evaluation"])
        self.assertFalse(payload["official_bao_gate_unblocked"])
        self.assertIn("derive_active_E_Z2Sigma_of_z", payload["next_required"])
        self.assertIn("derive_active_Gamma_drag_over_H0_Z2Sigma_of_z", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
