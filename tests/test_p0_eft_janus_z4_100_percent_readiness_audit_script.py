from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_100_percent_readiness_audit import build_payload, write_reports


class P0EFTJanusZ4100PercentReadinessAuditScriptTests(unittest.TestCase):
    def test_solver_complete_but_official_planck_not_claimed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["architecture_scaffold_complete"])
        self.assertTrue(payload["physical_prediction_complete"])
        self.assertEqual(payload["completion_fraction"], 1.0)
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertEqual(payload["remaining_blockers"], [])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_100_percent_readiness_audit.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_100_percent_readiness_audit.md").exists())
        self.assertGreater(payload["completion_fraction"], 0.0)


if __name__ == "__main__":
    unittest.main()
