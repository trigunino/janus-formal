import unittest

from scripts.derive_p0_eft_janus_z2_sigma_projective_holonomy_twist_derivation_target_gate import (
    build_payload,
)


class JanusZ2SigmaProjectiveHolonomyTwistDerivationTargetGateTest(unittest.TestCase):
    def test_twist_probe_is_not_promoted_without_derivation(self):
        payload = build_payload()
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["diagnostic_probe_available"])
        self.assertFalse(payload["diagnostic_probe_is_proof"])
        self.assertFalse(payload["projective_holonomy_twist_derived"])
        self.assertTrue(payload["obligations"]["deck_action_on_normal_frame"]["derived"])
        self.assertFalse(payload["R_Sigma_over_ell_collar_selection_promotable"])
        self.assertTrue(
            payload["obligations"]["collar_connection_from_active_metric"]["calculator_available"]
        )
        self.assertIn(
            "normal_connection_frame_primitives.json",
            payload["obligations"]["collar_connection_from_active_metric"]["missing_manifest"],
        )
        self.assertNotIn(
            "derive deck action on the normal frame bundle",
            payload["next_required"],
        )
        self.assertEqual(
            payload["primary_blocker"],
            "derive_deck_corrected_normal_holonomy_from_active_collar_metric",
        )

    def test_lists_required_holonomy_obligations(self):
        obligations = build_payload()["obligations"]
        self.assertIn("deck_action_on_normal_frame", obligations)
        self.assertIn("collar_connection_from_active_metric", obligations)
        self.assertIn("global_loop_closure", obligations)
        self.assertIn("non_flat_lambda_dependence", obligations)


if __name__ == "__main__":
    unittest.main()
