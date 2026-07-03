import unittest

from scripts.build_p0_eft_janus_sigma_boundary_variational_decomposition_gate import build_payload


class P0EFTJanusSigmaBoundaryVariationalDecompositionGateTests(unittest.TestCase):
    def test_variational_package_declared_and_boundary_action_closed(self):
        payload = build_payload()

        self.assertTrue(payload["sigma_boundary_variational_package_declared"])
        self.assertTrue(payload["variational_package"]["cartan_ghy_boundary_term_declared"])
        self.assertTrue(payload["variational_package"]["holst_nieh_yan_boundary_term_declared"])
        self.assertTrue(payload["variational_package"]["tetrad_variation_channel_declared"])
        self.assertTrue(payload["variational_package"]["connection_variation_channel_declared"])
        self.assertTrue(payload["variational_package"]["spinor_variation_channel_declared"])
        self.assertTrue(payload["variational_package"]["nonlinear_residual_obstruction_isolated"])
        self.assertTrue(payload["nonlinear_boundary_variation_closed"])
        self.assertTrue(payload["full_boundary_action_closed_on_sigma"])


if __name__ == "__main__":
    unittest.main()
