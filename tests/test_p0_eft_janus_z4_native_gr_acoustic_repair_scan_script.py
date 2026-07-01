from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_native_gr_acoustic_repair_scan import build_payload, write_reports


class P0EFTJanusZ4NativeGRAcousticRepairScanTests(unittest.TestCase):
    def test_projection_only_repair_is_tested_before_z4(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-native-gr-acoustic-repair-scan")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertTrue(payload["projection_only_hypothesis_tested"])
        self.assertIn("tt_projection_scan", payload)
        self.assertIn("te_projection_scan", payload)
        self.assertIn("ee_projection_scan", payload)
        self.assertIsInstance(payload["projection_only_sufficient"], bool)
        self.assertEqual(payload["native_source_repair_required"], not payload["projection_only_sufficient"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_acoustic_repair_scan.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_acoustic_repair_scan.md").exists())


if __name__ == "__main__":
    unittest.main()
