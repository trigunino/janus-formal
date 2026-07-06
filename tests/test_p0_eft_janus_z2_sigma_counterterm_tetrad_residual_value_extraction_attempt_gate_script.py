import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_residual_value_extraction_attempt_gate import (
    build_payload,
)


class CountertermTetradResidualValueExtractionAttemptGateTests(unittest.TestCase):
    def test_closure_has_component_schema_but_values_are_not_extractable(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["nonlinear_residual_closure_available"])
        self.assertFalse(payload["nonlinear_closure_is_boolean_only"])
        self.assertTrue(payload["component_emission"]["alpha_res_components_available"])
        self.assertTrue(payload["component_emission"]["alpha_res_component_decomposition_available"])
        self.assertFalse(payload["component_emission"]["alpha_res_component_values_available"])
        self.assertTrue(payload["tetrad_transport_ready"])
        self.assertTrue(payload["variational_formula_available"])
        self.assertFalse(payload["R_h_ab_value_extractable"])
        self.assertFalse(payload["R_K_ab_value_extractable"])
        self.assertEqual(payload["primary_blocker"], "nonlinear_closure_lacks_alpha_res_component_values")


if __name__ == "__main__":
    unittest.main()
