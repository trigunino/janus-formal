import unittest

from scripts.build_p0_eft_janus_z4_cmb_non_evidence_policy_gate import build_payload


class P0EFTJanusZ4CMBNonEvidencePolicyGateTests(unittest.TestCase):
    def test_z4_cmb_marked_non_evidence_and_active_core_is_z2(self):
        payload = build_payload()

        self.assertTrue(payload["z4_cmb_marked_non_evidence"])
        self.assertEqual(payload["active_core"], "Z2_tunnel_Sigma")
        self.assertTrue(payload["policy"]["z4_modules_diagnostic_only"])
        self.assertTrue(payload["policy"]["cyclic_z4_not_used_by_active_geometry"])
        self.assertTrue(payload["policy"]["active_core_is_z2_tunnel_sigma"])


if __name__ == "__main__":
    unittest.main()
