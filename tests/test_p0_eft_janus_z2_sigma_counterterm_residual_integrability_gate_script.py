import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_residual_integrability_gate import build_payload


class P0EFTJanusZ2SigmaCountertermResidualIntegrabilityGateTests(unittest.TestCase):
    def test_integrability_ledger_is_declared_without_fit(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_residual_integrability_ledger_declared"])
        self.assertEqual(payload["integrability_condition"], "d_field alpha_res = 0")
        self.assertIn("fitted exactness condition", payload["forbidden"])
        self.assertTrue(payload["declared"]["channel_cross_derivative_matrix_declared"])

    def test_integrability_remains_open_until_curl_is_computed(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["field_space_curl_computed"])
        self.assertFalse(payload["closure"]["residual_one_form_exact"])
        self.assertFalse(payload["counterterm_residual_integrability_ready"])
        self.assertIn("compute_field_space_curl_of_alpha_res", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
