from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_patch_scan_decision import build_payload


class P0EFTImmirziPatchScanDecisionTests(unittest.TestCase):
    def test_scan_decision_records_exclusion(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-patch-scan-decision-recorded")
        self.assertFalse(payload["planck_accepted"])
        self.assertTrue(payload["coherent_patch_simple_branch_excluded"])
        self.assertTrue(payload["supersedes_previous_single_gate"])


if __name__ == "__main__":
    unittest.main()
