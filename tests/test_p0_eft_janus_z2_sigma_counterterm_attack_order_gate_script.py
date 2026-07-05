import unittest

from scripts.build_p0_eft_janus_z2_sigma_counterterm_attack_order_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCountertermAttackOrderGateTests(unittest.TestCase):
    def test_attack_order_keeps_counterterm_blocker_upstream(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["declared"]["attack_order_is_diagnostic_only"])
        self.assertTrue(payload["declared"]["no_legacy_z4_import"])
        self.assertEqual(payload["primary_blocker"], "R_Sigma_solution_certificate")
        self.assertFalse(payload["closure"]["R_Sigma_solution_certificate_ready"])
        self.assertFalse(payload["closure"]["active_embedding_ready"])
        self.assertFalse(payload["gate_passed"])

    def test_tetrad_is_nearest_channel_but_not_ready(self):
        payload = build_payload()

        self.assertTrue(payload["closure"]["nearest_channel_identified"])
        self.assertTrue(payload["closure"]["tetrad_channel_is_nearest_not_ready"])
        self.assertIn("compute_tetrad_residual_channel", payload["attack_order"])
        self.assertIn("continue_R_Sigma_solution_frontier", payload["next_required"])
        self.assertFalse(
            payload["upstream_frontiers"]["residual_channel_frontier"]["ready"]
        )


if __name__ == "__main__":
    unittest.main()
