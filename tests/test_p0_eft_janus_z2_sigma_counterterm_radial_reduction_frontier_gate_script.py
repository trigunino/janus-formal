import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_radial_reduction_frontier_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermRadialReductionFrontierGateTests(unittest.TestCase):
    def test_counterterm_reduction_chain_is_declared(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["counterterm_radial_reduction_frontier_ledger_declared"])
        self.assertIn("alpha_res explicit", payload["reduction_chain"])
        self.assertTrue(payload["declared"]["no_fitted_counterterm_coefficient"])

    def test_counterterm_reduction_remains_blocked_until_chain_closes(self):
        payload = build_payload()

        self.assertFalse(payload["chain"]["residual_one_form_explicit"])
        self.assertFalse(payload["chain"]["counterterm_primitive_integrated"])
        self.assertFalse(payload["chain"]["counterterm_block_reduced"])
        self.assertFalse(payload["counterterm_radial_reduction_ready"])
        self.assertIn("feed_counterterm_block_reduced_to_throat_radius_solution_frontier", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
