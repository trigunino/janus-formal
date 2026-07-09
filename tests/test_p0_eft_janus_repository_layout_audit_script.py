import unittest

from scripts.build_p0_eft_janus_repository_layout_audit import build_payload


class P0EFTJanusRepositoryLayoutAuditTests(unittest.TestCase):
    def test_root_libs_and_branch_heads_are_clean(self):
        payload = build_payload()

        self.assertTrue(payload["root_facade_minimal"])
        self.assertEqual(payload["root_imports"], ["JanusFormal.Core"])
        self.assertTrue(payload["layout_clean"])
        self.assertEqual(payload["old_umbrellas_present"], [])
        self.assertFalse(payload["old_attempts_catchall_dir_present"])
        self.assertIn("Z2SigmaRegularThroat", payload["branch_heads"])
        self.assertIn("Z4CMBTopologyResetBlockedProgram", payload["branch_heads"])
        self.assertIn("P0BimetricOrbifoldPrototypeProgram", payload["branch_heads"])
        self.assertIn("P0EFTOrbifoldHolstPrototypeProgram", payload["branch_heads"])
        self.assertIn("Foundation", payload["shared_heads"])

    def test_daily_commands_do_not_use_global_archive(self):
        payload = build_payload()

        self.assertIn("lake build JanusFormal", payload["daily_commands"])
        self.assertIn("lake build JanusFormal.Branches.Z2SigmaRegularThroat", payload["daily_commands"])
        self.assertTrue(all("AllImportsArchive" not in item for item in payload["daily_commands"]))
        self.assertGreater(payload["diagnostic_z4_script_count"], 0)


if __name__ == "__main__":
    unittest.main()
