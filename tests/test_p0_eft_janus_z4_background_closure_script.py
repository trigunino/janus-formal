from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_background_closure import build_payload, write_reports


class P0EFTJanusZ4BackgroundClosureScriptTests(unittest.TestCase):
    def test_background_closure_scaffold_tracks_master_density(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["master_density"], "B*rho_minus + rho_plus")
        self.assertEqual(payload["zero_coupling_residual"], "0")
        self.assertTrue(payload["background_scaffold_ready"])
        self.assertFalse(payload["background_physical_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_closure.md").exists())
        self.assertIn("Friedmann", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
