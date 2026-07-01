from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_obstruction_ward_identity import build_payload, write_reports


class P0EFTJanusZ4ObstructionWardIdentityScriptTests(unittest.TestCase):
    def test_obstruction_is_reduced_to_ward_anomaly_balance(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["weighted_residual"], "0")
        self.assertEqual(payload["ward_residual"], "0")
        self.assertEqual(payload["closed_if_anomaly_free"], "0")
        self.assertTrue(payload["obstruction_ward_identity_ready"])
        self.assertFalse(payload["anomaly_cancellation_derived"])
        self.assertFalse(payload["full_action_variation_closed"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_obstruction_ward_identity.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_obstruction_ward_identity.md").exists())
        self.assertIn("full nonlinear gauge symmetry", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
