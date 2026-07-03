import unittest

from scripts.build_p0_eft_janus_z2_sigma_background_equation_derivation_gate import build_payload


class P0EFTJanusZ2SigmaBackgroundEquationDerivationGateTests(unittest.TestCase):
    def test_background_equations_block_until_derived_from_sigma(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["sigma_boundary_action_closed"])
        self.assertTrue(payload["background_bibliography_checked"])
        self.assertTrue(payload["local_background_derivation_required"])
        self.assertTrue(payload["projected_stress_tensor_gate_passed"])
        self.assertTrue(payload["tunnel_junction_condition_gate_passed"])
        self.assertTrue(payload["effective_background_closure_gate_passed"])
        self.assertTrue(payload["derived"]["projected_sigma_stress_tensor_derived"])
        self.assertTrue(payload["derived"]["z2_tunnel_junction_condition_derived"])
        self.assertTrue(payload["derived"]["effective_friedmann_equation_derived"])
        self.assertTrue(payload["derived"]["effective_acceleration_equation_derived"])
        self.assertTrue(payload["derived"]["effective_continuity_equation_derived"])
        self.assertTrue(payload["legacy_lcdm_background_substitution_forbidden"])
        self.assertTrue(payload["archived_z4_background_reuse_forbidden"])
        self.assertTrue(payload["background_equation_lock_closed"])
        self.assertTrue(payload["background_equations_derived"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertEqual(payload["next_required"], [])


if __name__ == "__main__":
    unittest.main()
