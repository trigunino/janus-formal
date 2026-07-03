import unittest

from scripts.build_p0_eft_janus_z2_sigma_coframe_connection_pullback_readiness_gate import (
    build_payload,
)


class P0EFTJanusZ2SigmaCoframeConnectionPullbackReadinessGateTests(unittest.TestCase):
    def test_standard_pullback_formulae_are_closed(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["coframe_connection_pullback_readiness_ledger_declared"])
        self.assertTrue(payload["readiness"]["differential_form_pullback_ready"])
        self.assertTrue(payload["readiness"]["coframe_pullback_formula_ready"])
        self.assertTrue(payload["readiness"]["spin_connection_pullback_formula_ready"])

    def test_active_embedding_still_blocks_actual_pullbacks(self):
        payload = build_payload()

        self.assertFalse(payload["readiness"]["active_embedding_ready"])
        self.assertFalse(payload["readiness"]["tangent_frame_ready"])
        self.assertFalse(payload["readiness"]["coframe_pullback_ready"])
        self.assertFalse(payload["coframe_connection_pullback_readiness_ready"])


if __name__ == "__main__":
    unittest.main()
