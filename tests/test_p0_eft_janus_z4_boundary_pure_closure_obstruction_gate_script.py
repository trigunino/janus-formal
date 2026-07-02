import unittest

from scripts.build_p0_eft_janus_z4_boundary_pure_closure_obstruction_gate import build_payload


class P0EFTJanusZ4BoundaryPureClosureObstructionGateTests(unittest.TestCase):
    def test_nonlinear_boundary_variation_blocks_post_counterterm_closure(self):
        payload = build_payload()

        self.assertTrue(payload["standard_source_no_go"])
        self.assertTrue(payload["eft_counterterm_algebraic_closure_available"])
        self.assertTrue(payload["counterterm_derived_from_janus_invariant"])
        self.assertFalse(payload["nonlinear_boundary_variation_closed"])
        self.assertFalse(payload["pure_boundary_closure_available"])
        self.assertFalse(payload["full_boundary_action_closed"])
        self.assertEqual(
            payload["remaining_boundary_obligation"],
            "close_nonlinear_boundary_variation",
        )
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
