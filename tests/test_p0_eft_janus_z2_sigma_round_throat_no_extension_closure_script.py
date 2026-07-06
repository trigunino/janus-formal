import unittest

from scripts.derive_p0_eft_janus_z2_sigma_round_throat_no_extension_closure import (
    build_payload,
)


class JanusZ2SigmaRoundThroatNoExtensionClosureScriptTest(unittest.TestCase):
    def test_zero_source_hk_branch_does_not_select_radius(self):
        payload = build_payload()

        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertFalse(payload["extension_allowed"])
        self.assertTrue(payload["source_terms_zero"])
        self.assertFalse(payload["radius_selection_ready"])
        self.assertFalse(payload["R_Sigma_solution_certificate_ready"])
        constraints = payload["no_extension_zero_source_constraints"]
        self.assertEqual(
            constraints["zero_for_all_positive_R_constraints"]["a0"], "0"
        )
        self.assertEqual(
            constraints["zero_for_all_positive_R_constraints"]["a1"], "0"
        )
        self.assertEqual(
            constraints["zero_for_all_positive_R_constraints"]["a3"], "-3*a2"
        )
        self.assertFalse(constraints["radius_selected"])


if __name__ == "__main__":
    unittest.main()
