import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_extraction_gate import build_payload


class P0EFTJanusZ2SigmaCountertermResidualExtractionGateTests(unittest.TestCase):
    def test_residual_extraction_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_residual_extraction_ledger_declared"])
        self.assertTrue(payload["declared"]["boundary_variation_bibliography_checked"])
        self.assertTrue(payload["declared"]["residual_one_form_decomposition_gate_declared"])
        self.assertTrue(payload["declared"]["residual_integrability_gate_declared"])
        self.assertIn("new fitted counterterm coefficient", payload["forbidden"])
        self.assertIn("counterterm_condition", payload["structural_formulae"])

    def test_residual_extraction_remains_open_until_primitive_exists(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["counterterm_primitive_integrated"])
        self.assertFalse(payload["closure"]["L_ct_local_expansion_derived"])
        self.assertFalse(payload["counterterm_residual_extraction_ready"])
        self.assertIn("pass_counterterm_residual_one_form_decomposition_gate", payload["next_required"])
        self.assertIn("pass_counterterm_residual_integrability_gate", payload["next_required"])
        self.assertIn("integrate_unique_counterterm_primitive", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
