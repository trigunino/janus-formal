from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_observable_oscilloscope import build_payload, write_reports


class P0EFTJanusZ4ObservableOscilloscopeTests(unittest.TestCase):
    def test_diagnostics_are_finite_without_planck_claim(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-observable-oscilloscope")
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertTrue(payload["gr_baseline_mode"])
        self.assertTrue(payload["finite_diagnostics"])
        self.assertTrue(payload["observable_oscilloscope_ready"])
        self.assertEqual(payload["channel_norms"]["mu_minus_one"], 0.0)
        self.assertEqual(payload["channel_norms"]["mixed_sector"], 0.0)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_observable_oscilloscope.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_observable_oscilloscope.md").exists())


if __name__ == "__main__":
    unittest.main()
