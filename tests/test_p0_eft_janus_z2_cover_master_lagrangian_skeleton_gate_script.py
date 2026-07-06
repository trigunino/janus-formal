import unittest

from scripts.derive_p0_eft_janus_z2_cover_master_lagrangian_skeleton_gate import (
    build_payload,
)


class JanusZ2CoverMasterLagrangianSkeletonGateTests(unittest.TestCase):
    def test_declares_single_cover_action_skeleton(self):
        payload = build_payload()
        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["skeleton_declared"])
        self.assertFalse(payload["explicit_variation_ready"])
        self.assertIn("Integral_Mhat", payload["skeleton"]["S_master"])
        self.assertFalse(payload["guardrails"]["plus_sector_independent_action"])
        self.assertFalse(payload["guardrails"]["minus_sector_independent_action"])
        self.assertFalse(payload["guardrails"]["rho_eff_collapse_used"])
        self.assertFalse(payload["guardrails"]["z4_monodromy_used"])
        self.assertEqual(
            payload["primary_blocker"],
            "write_explicit_cover_lagrangian_and_variation",
        )


if __name__ == "__main__":
    unittest.main()
