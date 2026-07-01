from __future__ import annotations

import unittest

from scripts.build_p0_eft_immirzi_sign_convention_audit import build_payload


class P0EFTImmirziSignConventionAuditTests(unittest.TestCase):
    def test_sign_convention_audit_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "immirzi-sign-convention-audit-run")
        self.assertTrue(payload["all_camb_anchors_present"])
        self.assertTrue(payload["sign_conventions_checked"])
        self.assertTrue(payload["cambridge_safe_to_patch"])


if __name__ == "__main__":
    unittest.main()
