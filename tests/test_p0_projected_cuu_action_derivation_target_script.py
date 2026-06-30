from __future__ import annotations

import unittest

from scripts.build_p0_projected_cuu_action_derivation_target import build_payload


class P0ProjectedCuuActionDerivationTargetTests(unittest.TestCase):
    def test_derivation_target_is_open_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "action-derivation-target-open")
        self.assertFalse(payload["projected_cuu_identity_derived"])
        self.assertEqual(
            payload["pulled_dust_action_weak_congruence_artifact"],
            "p0_janus_pulled_dust_action_weak_congruence_proof",
        )
        self.assertFalse(payload["conditional_dust_closure_ready"])
        self.assertFalse(payload["prediction_ready"])
        self.assertTrue(all(not row["closed"] for row in payload["derivation_steps"]))

    def test_steps_cover_action_variation_force_mirror_integrability(self) -> None:
        steps = {row["step"] for row in build_payload()["derivation_steps"]}

        self.assertIn("pullback_dust_action", steps)
        self.assertIn("vary_phi_l", steps)
        self.assertIn("recover_connection_force", steps)
        self.assertIn("mirror_consistency", steps)
        self.assertIn("integrability", steps)

    def test_sufficiency_keeps_l_dlogb_and_pressure_explicit(self) -> None:
        sufficient = " ".join(build_payload()["sufficient_for_conditional_dust_closure"])

        self.assertIn("same L", sufficient)
        self.assertIn("DlogB", sufficient)
        self.assertIn("pressure/Pi", sufficient)


if __name__ == "__main__":
    unittest.main()
