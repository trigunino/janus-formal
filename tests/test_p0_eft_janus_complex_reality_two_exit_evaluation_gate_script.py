import unittest

from scripts.build_p0_eft_janus_complex_reality_two_exit_evaluation_gate import (
    build_payload,
)


class ComplexRealityTwoExitEvaluationGateTests(unittest.TestCase):
    def test_routes_are_ranked(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(
            payload["recommended_order"][0],
            "try_active_embedding_on_S2_first",
        )
        self.assertFalse(payload["any_exit_ready_now"])
        self.assertFalse(payload["alpha_generated_now"])

    def test_topology_alone_is_not_enough(self):
        payload = build_payload()

        self.assertIn(
            "aroundSigma alone, because it is a one-cycle",
            payload["topology_answer"]["insufficient_patterns"],
        )
        self.assertIn(
            "S2_throat with nonzero Omega_Sigma angular area component",
            payload["topology_answer"]["sufficient_patterns"],
        )


if __name__ == "__main__":
    unittest.main()
