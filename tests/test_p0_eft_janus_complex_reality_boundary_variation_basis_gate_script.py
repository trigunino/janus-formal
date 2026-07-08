import unittest

from scripts.build_p0_eft_janus_complex_reality_boundary_variation_basis_gate import (
    build_payload,
)


class ComplexRealityBoundaryVariationBasisGateTests(unittest.TestCase):
    def test_symbolic_variation_basis_is_declared(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["symbolic_boundary_variation_basis_ready"])
        self.assertIn(
            "symbolic_normal_embedding_displacement_channel",
            payload["what_this_closes"],
        )
        self.assertIn(
            "tangential_embedding_variation_marked_gauge",
            payload["what_this_closes"],
        )

    def test_active_density_still_blocked(self):
        payload = build_payload()

        self.assertFalse(payload["active_boundary_variation_basis_ready"])
        self.assertFalse(payload["KKS_boundary_density_evaluable_now"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "closed_boundary_two_cycle_declared",
            payload["still_missing_for_active_density"],
        )
        self.assertEqual(payload["next_gate"], "ComplexRealityClosedBoundaryTwoCycleGate")


if __name__ == "__main__":
    unittest.main()
