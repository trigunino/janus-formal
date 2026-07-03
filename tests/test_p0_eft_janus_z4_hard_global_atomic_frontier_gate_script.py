import unittest

from scripts.build_p0_eft_janus_z4_hard_global_atomic_frontier_gate import (
    build_payload,
)


class P0EFTJanusZ4HardGlobalAtomicFrontierGateTests(unittest.TestCase):
    def test_frontier_lists_narrow_unproved_targets_without_no_fit_promotion(self):
        payload = build_payload()

        self.assertEqual(
            payload["lean_module"],
            "P0EFTJanusZ4HardGlobalAtomicFrontierGate",
        )
        self.assertFalse(payload["aps_frontier_closed"])
        self.assertFalse(payload["orbifold_frontier_closed"])
        self.assertFalse(payload["aps_refined_gate_can_close"])
        self.assertFalse(payload["orbifold_refined_gate_can_close"])
        self.assertFalse(payload["pure_math_model_closed_without_axioms"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])
        self.assertTrue(
            payload["transport_maps"]["aps_frontier_to_refined_gate_transport_theorem"]
        )
        self.assertTrue(
            payload["transport_maps"]["orbifold_frontier_to_refined_gate_transport_theorem"]
        )
        self.assertTrue(
            payload["transport_maps"]["aps_pt_chain_to_frontier_transport_theorem"]
        )
        self.assertTrue(
            payload["transport_maps"][
                "aps_boundary_geometry_chain_to_frontier_transport_theorem"
            ]
        )
        self.assertTrue(
            payload["transport_maps"]["orbifold_flux_chain_to_frontier_transport_theorem"]
        )
        self.assertTrue(
            payload["transport_maps"][
                "orbifold_integer_flux_orientation_chain_to_frontier_transport_theorem"
            ]
        )
        self.assertTrue(
            payload["transport_maps"]["frontier_items_still_require_direct_proofs"]
        )
        self.assertTrue(payload["closure_policy"]["aps_direct_witness_required"])
        self.assertTrue(payload["closure_policy"]["orbifold_direct_witness_required"])
        self.assertTrue(payload["closure_policy"]["synthetic_true_closure_forbidden"])
        self.assertTrue(payload["closure_policy"]["imported_theorem_must_match_target"])
        self.assertIn("pin_minus_lift_constructed", payload["aps_frontier"])
        self.assertIn("uniqueness_of_two_to_one_ratio", payload["orbifold_frontier"])


if __name__ == "__main__":
    unittest.main()
