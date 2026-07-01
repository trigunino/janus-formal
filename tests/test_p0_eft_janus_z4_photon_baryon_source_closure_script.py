from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_photon_baryon_source_closure import build_payload, write_reports


class P0EFTJanusZ4PhotonBaryonSourceClosureScriptTests(unittest.TestCase):
    def test_thomson_drag_and_single_sector_residuals_cancel(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["weighted_drag_residual"], "0")
        self.assertEqual(payload["single_sector_photon_residual"], "0")
        self.assertEqual(payload["single_sector_baryon_residual"], "0")
        self.assertTrue(payload["photon_baryon_source_closure_ready"])
        self.assertFalse(payload["photon_baryon_hierarchy_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_source_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_source_closure.md").exists())
        self.assertIn("Boltzmann", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
