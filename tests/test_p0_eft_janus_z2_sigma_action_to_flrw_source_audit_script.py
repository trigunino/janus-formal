import unittest

from scripts.build_p0_eft_janus_z2_sigma_action_to_flrw_source_audit import build_payload


class SigmaActionToFLRWSourceAuditTests(unittest.TestCase):
    def test_current_admitted_action_derives_zero_sigma_source(self):
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["rho_Sigma_status"], "derived_zero_under_current_admitted_action")
        self.assertEqual(payload["rho_Sigma_a_values_over_rho_crit0"], [0.0, 0.0, 0.0])
        self.assertFalse(payload["E_Z2Sigma_a2_ready"])
        self.assertTrue(payload["nonzero_background_source_requires_extension"])

    def test_no_admitted_term_emits_homogeneous_source(self):
        payload = build_payload()

        self.assertEqual(payload["emitting_admitted_terms"], [])
        self.assertTrue(all(not term["emits_homogeneous_source"] for term in payload["admitted_terms"].values()))

    def test_extension_frontiers_are_not_admitted_sources(self):
        payload = build_payload()

        self.assertIn("LL_brane_null_source", payload["extension_frontiers"])
        self.assertFalse(payload["extension_frontiers"]["LL_brane_null_source"]["admitted_in_current_action"])


if __name__ == "__main__":
    unittest.main()
