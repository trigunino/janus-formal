from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_photon_baryon_nonproxy_closure import build_payload, write_reports


class P0EFTJanusZ4PhotonBaryonNonProxyClosureScriptTests(unittest.TestCase):
    def test_photon_baryon_closure_has_internal_drag_balance(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["sound_speed_squared"], "1/(3*(R + 1))")
        self.assertEqual(payload["drag_internal_residual"], "0")
        self.assertEqual(payload["single_sector_metric_residual"], "0")
        self.assertTrue(payload["photon_baryon_hierarchy_nonproxy"])
        self.assertTrue(payload["visibility_input_required"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_nonproxy_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_photon_baryon_nonproxy_closure.md").exists())
        self.assertIn("recombination visibility", payload["scope"])


if __name__ == "__main__":
    unittest.main()
