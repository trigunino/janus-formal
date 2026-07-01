from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_native_gr_decomposition_gate import build_payload, write_reports


class P0EFTJanusZ4NativeGRDecompositionGateTests(unittest.TestCase):
    def test_decomposition_gate_blocks_z4_until_native_gr_matches_camb(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-native-gr-decomposition-gate")
        self.assertEqual(payload["reference_solver"], "CAMB")
        self.assertFalse(payload["z4_sector_enabled"])
        self.assertFalse(payload["negative_sector_enabled"])
        self.assertFalse(payload["torsion_enabled"])
        self.assertFalse(payload["native_gr_matches_standard_gr"])
        self.assertFalse(payload["z4_corrections_allowed"])
        self.assertTrue(payload["physical_planck_interpretation_suspended"])
        self.assertIn("background_geometry", payload)
        self.assertIn("visibility", payload)
        self.assertIn("fixed_k_sources", payload)
        self.assertIn("unlensed_proxy_spectra", payload)
        self.assertIn("lensing_split", payload)
        self.assertGreaterEqual(len(payload["primary_blockers"]), 3)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_decomposition_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_gr_decomposition_gate.md").exists())


if __name__ == "__main__":
    unittest.main()
