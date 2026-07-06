import unittest

from scripts.build_p0_eft_janus_sigma_boundary_nonlinear_residual_closure_gate import build_payload


class P0EFTJanusSigmaBoundaryNonlinearResidualClosureGateTests(unittest.TestCase):
    def test_unique_sigma_counterterm_closes_full_boundary_action(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_nonlinear_boundary_residual_closed"])
        self.assertTrue(payload["sigma_full_boundary_action_closed"])
        self.assertTrue(payload["closure"]["sigma_supported_counterterm_unique"])
        self.assertTrue(payload["closure"]["counterterm_variation_cancels_residual"])
        self.assertTrue(payload["closure"]["tetrad_channel_closed"])
        self.assertTrue(payload["closure"]["connection_channel_closed"])
        self.assertTrue(payload["closure"]["spinor_channel_closed"])
        self.assertFalse(payload["nonlinear_closure_is_boolean_only"])
        self.assertTrue(payload["nonlinear_closure_emits_component_schema_only"])
        self.assertTrue(payload["component_emission"]["alpha_res_components_available"])
        self.assertTrue(payload["component_emission"]["alpha_res_component_decomposition_available"])
        self.assertFalse(payload["component_emission"]["alpha_res_component_values_available"])
        self.assertIn("metric_tetrad_component", payload["component_emission"]["alpha_res_component_names"])
        self.assertIn("emit_alpha_res_component_values", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
