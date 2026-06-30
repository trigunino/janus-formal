from __future__ import annotations

import unittest

from scripts.build_temporary_scaffolds_audit import build_payload


class TemporaryScaffoldsAuditTests(unittest.TestCase):
    def test_audit_marks_blocking_scaffolds_and_keepers(self) -> None:
        payload = build_payload()

        self.assertGreater(payload["temporary_count"], 0)
        self.assertGreater(payload["keeper_count"], 0)
        self.assertTrue(any(item["item"].startswith("Q_det") for item in payload["items"]))
        self.assertTrue(
            any(item["item"] == "H0^-1 PM time calibration" for item in payload["items"])
        )


if __name__ == "__main__":
    unittest.main()
