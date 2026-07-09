import unittest

from scripts.build_p0_eft_janus_z2_sigma_branch_head_audit import build_payload


class P0EFTJanusZ2SigmaBranchHeadAuditTests(unittest.TestCase):
    def test_z2_sigma_branch_uses_split_branch_head(self):
        payload = build_payload()

        self.assertTrue(payload["root_facade_minimal"])
        self.assertEqual(payload["root_imports"], ["JanusFormal.Core"])
        self.assertEqual(
            payload["branch_head"], "JanusFormal/Branches/Z2SigmaRegularThroat.lean"
        )
        self.assertTrue(payload["branch_head_split"])
        self.assertTrue(payload["branch_layout_clean"])
        self.assertEqual(payload["old_facades_present"], [])
        self.assertGreater(payload["subhead_import_counts"]["Topology"], 0)
        self.assertGreater(payload["subhead_import_counts"]["Observables"], 0)


if __name__ == "__main__":
    unittest.main()
