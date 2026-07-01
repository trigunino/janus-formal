from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_postfix_validity_audit import build_payload


class P0EFTCMBPostFixValidityAuditTests(unittest.TestCase):
    def test_invalidated_and_postfix_reports_are_classified(self) -> None:
        payload = build_payload()

        statuses = {row["report"]: row["validity"] for row in payload["rows"]}
        self.assertEqual(statuses["p0_eft_immirzi_geff_planck_gate.json"], "post_fix_valid")
        self.assertEqual(statuses["p0_eft_immirzi_consistent_patch_planck_gate.json"], "post_fix_valid")
        self.assertEqual(statuses["p0_eft_coherent_primordial_immirzi_planck_gate.json"], "post_fix_valid")
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
