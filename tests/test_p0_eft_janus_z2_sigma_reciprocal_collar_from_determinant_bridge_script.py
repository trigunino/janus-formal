import unittest

from scripts.derive_p0_eft_janus_z2_sigma_reciprocal_collar_from_determinant_bridge import (
    build_payload,
)


class JanusZ2SigmaReciprocalCollarFromDeterminantBridgeScriptTest(unittest.TestCase):
    def test_determinant_bridge_identifies_exact_missing_lambda_law(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertTrue(payload["formal_bridge_reciprocal_identity_declared"])
        self.assertFalse(payload["active_pullback_reciprocal_identity_derived"])
        self.assertFalse(payload["active_lambda_law_derived"])
        self.assertTrue(payload["reciprocal_probe_selects_ratio"])
        self.assertEqual(payload["candidate_ratio"], 1.0)
        self.assertFalse(payload["promotion_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "derive_B_plus_lambda_equals_lambda_minus_six_from_active_embedding",
        )


if __name__ == "__main__":
    unittest.main()
