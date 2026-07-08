import unittest

from scripts.build_p0_eft_janus_complex_reality_combined_phase_space_candidate_gate import (
    build_payload,
)


class ComplexRealityCombinedPhaseSpaceCandidateGateTests(unittest.TestCase):
    def test_combined_candidate_is_coherent(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["combined_candidate_coherent"])
        self.assertEqual(
            payload["combined_candidate"]["name"],
            "S2_throat_CP1_fiber_aroundSigma_holonomy",
        )
        self.assertIn("CP1 quantizable fiber", payload["what_it_combines"])

    def test_combined_candidate_is_not_closed(self):
        payload = build_payload()

        self.assertFalse(payload["combined_candidate_physically_closed"])
        self.assertFalse(payload["alpha_generated_now"])
        self.assertIn("aroundSigma_action_on_CP1_derived", payload["still_missing"])
        self.assertEqual(payload["next_gate"], "ComplexRealityAroundSigmaCP1HolonomyActionGate")


if __name__ == "__main__":
    unittest.main()
