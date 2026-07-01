from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_scalar_closure import build_payload, write_reports


class P0EFTJanusZ4ScalarClosureScriptTests(unittest.TestCase):
    def test_scalar_closure_scaffold_tracks_master_sources(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["master_delta"], "B*delta_rho_minus + delta_rho_plus")
        self.assertEqual(payload["zero_coupling_residual"], "0")
        self.assertTrue(payload["scalar_closure_scaffold_ready"])
        self.assertFalse(payload["scalar_closure_physical_ready"])
        self.assertIn("Phi - Psi", payload["slip"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_closure.md").exists())
        self.assertIn("Bianchi", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
