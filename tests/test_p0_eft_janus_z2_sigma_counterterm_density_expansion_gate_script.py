import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_density_expansion_gate import build_payload


class P0EFTJanusZ2SigmaCountertermDensityExpansionGateTests(unittest.TestCase):
    def test_density_expansion_ledger_is_declared_without_new_freedom(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_density_expansion_ledger_declared"])
        self.assertTrue(payload["declared"]["counterterm_local_density_basis_gate_declared"])
        self.assertTrue(payload["declared"]["counterterm_residual_extraction_gate_declared"])
        self.assertIn("new fitted counterterm coefficient", payload["forbidden"])
        self.assertTrue(payload["declared"]["no_new_counterterm_freedom_declared"])

    def test_explicit_density_expansion_remains_open(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["L_ct_expanded_in_active_variables"])
        self.assertFalse(payload["counterterm_density_expansion_ready"])
        self.assertIn("pass_counterterm_local_density_basis_gate", payload["next_required"])
        self.assertIn("pass_counterterm_residual_extraction_gate", payload["next_required"])
        self.assertIn("expand_L_ct_in_h_K_torsion_Immirzi_variables", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
