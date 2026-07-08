import unittest

from scripts.build_p0_eft_janus_complex_reality_around_sigma_cp1_holonomy_action_gate import (
    build_payload,
)


class ComplexRealityAroundSigmaCP1HolonomyActionGateTests(unittest.TestCase):
    def test_holonomy_actions_are_classified(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["holonomy_action_symbolically_classified"])
        self.assertEqual(
            payload["actions"]["central_spin_lift_minus_identity"]["action_on_CP1"],
            "trivial",
        )

    def test_holonomy_action_is_not_derived(self):
        payload = build_payload()

        self.assertFalse(payload["aroundSigma_action_on_CP1_derived"])
        self.assertIn("spin_lift_of_aroundSigma_specified", payload["still_missing"])
        self.assertIn("noncentral_projective_action_derived", payload["still_missing"])


if __name__ == "__main__":
    unittest.main()
