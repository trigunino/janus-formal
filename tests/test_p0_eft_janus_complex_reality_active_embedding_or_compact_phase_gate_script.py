import unittest

from scripts.build_p0_eft_janus_complex_reality_active_embedding_or_compact_phase_gate import (
    build_payload,
)


class ComplexRealityActiveEmbeddingOrCompactPhaseGateTests(unittest.TestCase):
    def test_two_remaining_routes_are_explicit(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["active_embedding_route"]["route"],
            "active_embedding_pullback_on_throat_S2",
        )
        self.assertEqual(
            payload["compact_phase_route"]["route"],
            "aroundSigma_cross_compact_frame_phase",
        )

    def test_no_nonzero_kks_period_route_ready_yet(self):
        payload = build_payload()

        self.assertFalse(payload["active_embedding_route"]["ready"])
        self.assertFalse(payload["compact_phase_route"]["ready"])
        self.assertFalse(payload["nonzero_KKS_boundary_period_route_ready"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "compact_frame_phase_derived",
            payload["still_missing"]["compact_phase_route"],
        )


if __name__ == "__main__":
    unittest.main()
