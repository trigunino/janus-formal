from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_negative_sector_cmb_imprint import build_payload, write_reports


class P0EFTJanusNegativeSectorCMBImprintTests(unittest.TestCase):
    def test_negative_sector_imprint_is_branch_only_and_fixed_ratio(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-negative-sector-cmb-imprint")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertFalse(payload["continuous_fit_factor_used"])
        self.assertEqual(payload["source_reference"]["fixed_scale_ratio"], 100.0)
        self.assertEqual(payload["source_reference"]["fixed_c_ratio"], 10.0)
        self.assertGreater(len(payload["candidates"]), 0)
        self.assertIsInstance(payload["accepted_candidate_count"], int)
        self.assertIsInstance(payload["safe_to_promote"], bool)
        self.assertIn("best_promotable_candidate", payload)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_negative_sector_cmb_imprint.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_negative_sector_cmb_imprint.md").exists())


if __name__ == "__main__":
    unittest.main()
