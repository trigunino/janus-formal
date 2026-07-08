import unittest

from scripts.build_p0_eft_janus_complex_reality_closed_boundary_two_cycle_gate import (
    build_payload,
)


class ComplexRealityClosedBoundaryTwoCycleGateTests(unittest.TestCase):
    def test_topological_cycles_are_audited(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["topological_cycle_audit_ready"])
        self.assertIn(
            "closed_topological_throat_S2_identified",
            payload["what_this_closes"],
        )
        self.assertEqual(payload["cycle_candidates"]["aroundSigma_Z2"]["dimension"], 1)

    def test_kks_boundary_two_cycle_still_not_ready(self):
        payload = build_payload()

        self.assertFalse(payload["KKS_boundary_two_cycle_ready"])
        self.assertFalse(payload["KKS_boundary_period_nonzero"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn(
            "closed_KKS_phase_space_two_cycle_declared",
            payload["still_missing_for_integrality"],
        )
        self.assertEqual(payload["next_gate"], "ComplexRealityActiveEmbeddingOrCompactPhaseGate")


if __name__ == "__main__":
    unittest.main()
