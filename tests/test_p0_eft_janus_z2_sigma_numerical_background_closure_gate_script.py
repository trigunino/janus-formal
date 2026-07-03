import unittest

from scripts.build_p0_eft_janus_z2_sigma_numerical_background_closure_gate import build_payload


class P0EFTJanusZ2SigmaNumericalBackgroundClosureGateTests(unittest.TestCase):
    def test_structural_background_is_not_yet_numeric_background(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["prerequisites"]["background_equations_derived"])
        self.assertTrue(payload["prerequisites"]["effective_fluid_structural_projection_ready"])
        self.assertFalse(payload["prerequisites"]["effective_fluid_numeric_closure_ready"])
        self.assertFalse(payload["prerequisites"]["active_tunnel_embedding_of_a_closure_ready"])
        self.assertFalse(payload["prerequisites"]["rho_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["prerequisites"]["p_eff_Z2Sigma_of_a_ready"])
        self.assertFalse(payload["numerical_background_prerequisites_ready"])
        self.assertFalse(payload["numerical_H_Z2Sigma_ready"])
        self.assertFalse(payload["numerical_Omega_m_Z2Sigma_ready"])

    def test_no_lcdm_or_z4_background_reuse(self):
        payload = build_payload()

        self.assertTrue(payload["prerequisites"]["observational_parameter_fit_forbidden"])
        self.assertTrue(payload["prerequisites"]["legacy_lcdm_background_reuse_forbidden"])
        self.assertTrue(payload["prerequisites"]["archived_z4_background_reuse_forbidden"])
        self.assertIn("X_plus_Z2Sigma(a)", payload["missing_functions"])
        self.assertIn("close_active_tunnel_embedding_of_a_gate", payload["next_required"])
        self.assertIn("implement_H_Z2Sigma_callable_without_lcdm_substitution", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
