import unittest

from scripts.build_p0_eft_janus_z2_sigma_toy_exact_throat_model_gate import (
    build_payload,
)


class JanusZ2SigmaToyExactThroatModelGateTests(unittest.TestCase):
    def test_toy_model_reports_parities_without_promoting_to_proof(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertEqual(payload["model_status"], "toy_diagnostic_only")
        self.assertEqual(payload["proof_status"], "not_a_proof_of_active_counterterm")
        self.assertEqual(payload["parity"]["h_ab"], "even")
        self.assertEqual(payload["parity"]["K_ab"], "odd")
        self.assertEqual(payload["parity"]["K_squared"], "even")
        self.assertTrue(payload["diagnostics"]["linear_K_terms_are_Z2_odd"])
        self.assertTrue(payload["diagnostics"]["quadratic_K_terms_are_Z2_even"])
        self.assertTrue(payload["diagnostics"]["finite_throat_does_not_force_E_counterterm_zero"])
        self.assertTrue(payload["diagnostics"]["point_collapse_is_singular_not_active_proof"])
        self.assertTrue(payload["diagnostics"]["does_not_validate_bridge_determinant_transport"])
        self.assertTrue(payload["diagnostics"]["does_not_source_derive_S_cross"])
        self.assertTrue(payload["diagnostics"]["does_not_close_Bianchi"])


if __name__ == "__main__":
    unittest.main()
