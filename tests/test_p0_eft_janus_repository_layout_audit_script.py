import unittest

from scripts.build_p0_eft_janus_repository_layout_audit import build_payload


class P0EFTJanusRepositoryLayoutAuditTests(unittest.TestCase):
    def test_root_facade_is_minimal_and_active_only(self):
        payload = build_payload()

        self.assertTrue(payload["root_facade_minimal"])
        self.assertEqual(payload["root_imports"], ["JanusFormal.ActiveZ2Sigma"])
        self.assertTrue(payload["layout_clean"])
        self.assertEqual(payload["forbidden_root_archive_imports"], [])
        self.assertEqual(payload["forbidden_active_z4_imports"], [])

    def test_archive_is_optional_not_daily(self):
        payload = build_payload()

        self.assertIn("lake build JanusFormal", payload["daily_commands"])
        self.assertNotIn("lake build JanusFormal.AllImportsArchive", payload["daily_commands"])
        self.assertIn("lake build JanusFormal.AllImportsArchive", payload["archive_commands_optional"])
        self.assertGreater(payload["legacy_z4_script_count"], 0)


if __name__ == "__main__":
    unittest.main()
