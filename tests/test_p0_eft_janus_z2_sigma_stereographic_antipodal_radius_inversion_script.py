import unittest

from scripts.derive_p0_eft_janus_z2_sigma_stereographic_antipodal_radius_inversion import (
    build_payload,
)


class JanusZ2SigmaStereographicAntipodalRadiusInversionScriptTest(unittest.TestCase):
    def test_projective_antipodal_map_supplies_reciprocal_radius_law(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertEqual(payload["radius_law"], "r -> 1/r")
        self.assertEqual(payload["candidate_R_Sigma_over_ell_collar"], 1.0)
        self.assertFalse(payload["promotion_ready"])
        self.assertEqual(
            payload["primary_blocker"],
            "prove_active_tunnel_lambda_is_the_projective_stereographic_radius",
        )


if __name__ == "__main__":
    unittest.main()
