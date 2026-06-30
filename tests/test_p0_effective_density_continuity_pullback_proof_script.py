from __future__ import annotations

import unittest

from scripts.build_p0_effective_density_continuity_pullback_proof import build_payload


class P0EffectiveDensityContinuityPullbackProofTests(unittest.TestCase):
    def test_pullback_theorem_and_field_source_anchor_closed_but_action_bridge_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["target_identity"], "D_receiver(B_4vol rho_to u_to)=0")
        self.assertTrue(payload["standard_source_continuity_closed"])
        self.assertTrue(payload["pullback_vector_density_theorem_closed"])
        self.assertTrue(payload["janus_field_source_measure_anchored"])
        self.assertFalse(payload["pulled_action_measure_anchored"])
        self.assertTrue(payload["single_cross_dust_effective_continuity_closed"])
        self.assertFalse(payload["effective_density_continuity_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_derivation_contains_source_measure_and_commuting_divergence(self) -> None:
        claims = " ".join(row["claim"] for row in build_payload()["derivation_steps"])

        self.assertIn("source dust action gives", claims)
        self.assertIn("B_4vol rho_to u_to", claims)
        self.assertIn("receiver divergence commutes with pullback", claims)
        self.assertIn("phi^*(D_source", claims)

    def test_forbids_scalar_absorption_and_keeps_janus_source_row_open(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["forbidden_shortcuts"])
        open_rows = " ".join(payload["open_source_rows"])

        self.assertIn("Q_cross", forbidden)
        self.assertIn("dust 3-volume", forbidden)
        self.assertIn("same map", open_rows)
        self.assertIn("pulled dust action", open_rows)


if __name__ == "__main__":
    unittest.main()
