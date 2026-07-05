import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_omega_k_derivation_gate import build_payload


class P0EFTJanusZ2SigmaActiveOmegaKDerivationGateTests(unittest.TestCase):
    def test_omega_k_formula_is_ready_but_values_are_blocked(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["projective_tunnel_two_fold_topology_ready"])
        self.assertFalse(payload["topology_alone_fixes_numeric_omega_k"])
        self.assertTrue(payload["omega_k_formula_builder_ready"])
        self.assertTrue(payload["requires_active_H0_Z2Sigma"])
        self.assertTrue(payload["requires_curvature_sign_k_Z2Sigma"])
        self.assertFalse(payload["curvature_sign_gate_passed"])
        self.assertFalse(payload["curvature_sign_values_ready"])
        self.assertFalse(payload["topology_alone_fixes_FLRW_curvature_sign"])
        self.assertTrue(payload["requires_active_FLRW_curvature_radius_or_embedding_scale"])
        self.assertTrue(payload["requires_active_R_Sigma_or_embedding_solution"])
        self.assertFalse(payload["omega_k_Z2Sigma_values_ready"])
        self.assertFalse(payload["background_curvature_normalization_inputs_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_omega_k_gate_forbids_compressed_or_archived_inputs(self):
        payload = build_payload()

        self.assertFalse(payload["uses_compressed_planck_lcdm_background"])
        self.assertFalse(payload["uses_archived_z4_background"])
        self.assertFalse(payload["uses_observational_H0_fit"])


if __name__ == "__main__":
    unittest.main()
