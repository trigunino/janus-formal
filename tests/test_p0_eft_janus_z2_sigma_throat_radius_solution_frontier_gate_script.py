import unittest

from scripts.build_p0_eft_janus_z2_sigma_throat_radius_solution_frontier_gate import build_payload


class P0EFTJanusZ2SigmaThroatRadiusSolutionFrontierGateTests(unittest.TestCase):
    def test_frontier_ledger_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["throat_radius_solution_frontier_ledger_declared"])
        self.assertTrue(payload["status_flags"]["variational_equation_ready"])
        self.assertTrue(payload["status_flags"]["conditional_embedding_map_ready"])

    def test_solution_certificate_remains_blocked_by_two_radial_blocks(self):
        payload = build_payload()

        self.assertFalse(payload["status_flags"]["matter_flux_block_reduced"])
        self.assertFalse(payload["status_flags"]["counterterm_block_reduced"])
        self.assertFalse(payload["throat_radius_solution_certificate_ready"])
        self.assertFalse(payload["embedding_unblocked_by_radius_solution"])
        self.assertIn("matter_flux_block_reduced = false via MatterFluxFrontierGate", payload["current_frontier"])
        self.assertIn("counterterm_block_reduced = false", payload["current_frontier"])


if __name__ == "__main__":
    unittest.main()
