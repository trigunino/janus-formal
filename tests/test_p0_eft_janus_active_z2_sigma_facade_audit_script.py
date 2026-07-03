import unittest

from scripts.build_p0_eft_janus_active_z2_sigma_facade_audit import build_payload


class P0EFTJanusActiveZ2SigmaFacadeAuditTests(unittest.TestCase):
    def test_active_facade_imports_only_z2_sigma_surface(self):
        payload = build_payload()

        self.assertTrue(payload["root_facade_minimal"])
        self.assertEqual(payload["root_imports"], ["JanusFormal.ActiveZ2Sigma"])
        self.assertEqual(payload["active_facade"], "JanusFormal/ActiveZ2Sigma.lean")
        self.assertTrue(payload["active_facade_z2_sigma_only"])
        self.assertTrue(payload["legacy_z4_archive_policy_imported"])
        self.assertEqual(payload["unexpected_imports"], [])
        self.assertEqual(payload["forbidden_active_z4_imports"], [])
        self.assertEqual(payload["forbidden_cmb_planck_imports"], [])


if __name__ == "__main__":
    unittest.main()
