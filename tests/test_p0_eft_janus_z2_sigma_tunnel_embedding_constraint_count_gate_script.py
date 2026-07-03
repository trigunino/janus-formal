import unittest

from scripts.build_p0_eft_janus_z2_sigma_tunnel_embedding_constraint_count_gate import build_payload


class P0EFTJanusZ2SigmaTunnelEmbeddingConstraintCountGateTests(unittest.TestCase):
    def test_constraint_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["embedding_constraint_ledger_declared"])
        self.assertTrue(payload["declared"]["throat_radius_law_gate_declared"])
        self.assertTrue(payload["declared"]["throat_radius_variational_equation_gate_declared"])
        self.assertTrue(payload["declared"]["throat_radius_variational_equation_ready"])
        self.assertTrue(payload["declared"]["throat_radius_block_expansion_gate_declared"])
        self.assertTrue(payload["declared"]["throat_radius_block_ledger_declared"])
        self.assertTrue(payload["declared"]["embedding_gauge_policy_gate_declared"])
        self.assertTrue(payload["declared"]["embedding_gauge_equation_gate_declared"])
        self.assertTrue(payload["declared"]["embedding_gauge_equations_ready"])
        self.assertIn("R_Sigma(a)", payload["unknown_functions"])
        self.assertGreater(payload["unknown_function_count"], 0)

    def test_embedding_closure_requires_throat_radius_and_gauge(self):
        payload = build_payload()

        self.assertFalse(payload["closure"]["throat_radius_law_derived"])
        self.assertFalse(payload["closure"]["embedding_gauge_fixed"])
        self.assertFalse(payload["closure"]["X_plus_minus_of_a_determined"])
        self.assertFalse(payload["embedding_constraint_closure_ready"])
        self.assertIn("pass_throat_radius_law_gate", payload["missing_to_close"])
        self.assertIn("solve_throat_radius_variational_equation_for_R_Sigma_of_a", payload["missing_to_close"])
        self.assertIn("reduce_all_throat_radius_radial_blocks", payload["missing_to_close"])
        self.assertIn("pass_embedding_gauge_policy_gate", payload["missing_to_close"])
        self.assertIn("insert_throat_radius_law_into_embedding_gauge_equations", payload["missing_to_close"])


if __name__ == "__main__":
    unittest.main()
