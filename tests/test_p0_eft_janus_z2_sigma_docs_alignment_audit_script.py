import unittest

from scripts.build_p0_eft_janus_z2_sigma_docs_alignment_audit import build_payload


class P0EFTJanusZ2SigmaDocsAlignmentAuditTests(unittest.TestCase):
    def test_docs_do_not_present_z4_as_active(self):
        payload = build_payload()

        self.assertEqual(payload["forbidden_active_z4_snippets"], [])
        self.assertTrue(payload["docs_aligned_to_z2_sigma"])
        self.assertTrue(payload["required_markers"]["active_geometry_core_declared"])
        self.assertTrue(payload["required_markers"]["z4_cmb_non_evidence_declared"])
        self.assertTrue(payload["required_markers"]["active_audit_declared"])


if __name__ == "__main__":
    unittest.main()
