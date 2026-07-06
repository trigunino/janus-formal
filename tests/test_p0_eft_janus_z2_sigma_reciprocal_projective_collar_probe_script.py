import unittest

from scripts.derive_p0_eft_janus_z2_sigma_reciprocal_projective_collar_probe import (
    build_payload,
)


class JanusZ2SigmaReciprocalProjectiveCollarProbeScriptTest(unittest.TestCase):
    def test_reciprocal_probe_selects_ratio_but_remains_unpromoted(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertTrue(payload["R_Sigma_over_ell_collar_selected"])
        self.assertEqual(payload["candidate_ratio"], 1.0)
        self.assertFalse(payload["promotion_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "derive_reciprocal_projective_collar_map_from_Janus_tunnel_geometry",
        )


if __name__ == "__main__":
    unittest.main()
