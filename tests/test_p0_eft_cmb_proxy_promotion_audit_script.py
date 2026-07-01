from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_proxy_promotion_audit import build_payload


class P0EFTCMBProxyPromotionAuditTests(unittest.TestCase):
    def test_promotion_audit_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-proxy-promotion-audit-open")
        self.assertTrue(payload["proxy_pipeline_ready"])
        self.assertGreater(payload["open_replacement_count"], 0)

    def test_direct_cmb_prediction_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["is_planck_verdict"])
        self.assertFalse(payload["direct_cmb_prediction_ready"])


if __name__ == "__main__":
    unittest.main()
