from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_native_gr_reference_gate import build_payload, write_reports


class P0EFTJanusZ4NativeGRReferenceGateTests(unittest.TestCase):
    def test_native_gr_reference_gate_compares_against_camb(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-native-gr-reference-gate")
        self.assertEqual(payload["reference_solver"], "CAMB")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertFalse(payload["compressed_lcdm_parameters_used_for_validation"])
        self.assertIn("high_tt", payload["shape"])
        self.assertIn("tt_first_peak", payload)
        self.assertIsInstance(payload["native_gr_matches_standard_gr"], bool)
        self.assertEqual(payload["z4_corrections_allowed"], payload["native_gr_matches_standard_gr"])

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_reference_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_reference_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
