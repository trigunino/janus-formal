from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_emode_projection_scan import build_payload


class P0EFTJanusZ4EModeProjectionScanScriptTests(unittest.TestCase):
    def test_emode_scan_can_run_without_official_likelihood(self) -> None:
        payload = build_payload(scales=(0.7, 1.0), execute_official=False)

        self.assertTrue(payload["emode_projection_scan_ready"])
        self.assertTrue(payload["native_z4_solver_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertTrue(payload["active_scale_restored"])
        self.assertEqual(payload["active_scale"], 1.0)
        self.assertEqual(len(payload["rows"]), 2)
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_native_cmb_transfer_spectra.csv").exists())


if __name__ == "__main__":
    unittest.main()
