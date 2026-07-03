import unittest

from scripts.build_p0_eft_janus_z2_sigma_coupled_radius_flux_function_space_gate import build_payload


class P0EFTJanusZ2SigmaCoupledRadiusFluxFunctionSpaceGateTests(unittest.TestCase):
    def test_function_space_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["function_space_ledger_declared"])
        self.assertIn("R_Sigma", payload["candidate_spaces"])
        self.assertTrue(payload["declared"]["no_distributional_product_ambiguity_declared"])

    def test_function_space_remains_blocked_until_analytic_obligations_close(self):
        payload = build_payload()

        self.assertFalse(payload["analytic_obligations"]["flux_functional_well_defined"])
        self.assertFalse(payload["analytic_obligations"]["embedding_trace_map_continuous"])
        self.assertFalse(payload["function_space_ready"])
        self.assertIn("function_space_ready_for_well_posedness = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
