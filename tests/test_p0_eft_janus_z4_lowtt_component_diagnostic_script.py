from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_lowtt_component_diagnostic import build_payload, write_reports


class P0EFTJanusZ4LowTTComponentDiagnosticScriptTests(unittest.TestCase):
    def test_lowtt_component_payload_exposes_sources(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["lowtt_component_diagnostic_ready"])
        self.assertTrue(payload["native_z4_solver_used"])
        self.assertFalse(payload["compressed_lcdm_parameters_used"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        self.assertIn(payload["dominant_lowtt_source"], {"sw", "doppler", "isw"})
        self.assertGreaterEqual(len(payload["rows"]), 20)
        self.assertIn("chi2_per_dof", payload["lowtt_shape_proxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lowtt_component_diagnostic.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_lowtt_component_diagnostic.md").exists())
        self.assertTrue(payload["official_lowl_tt_rejected_elsewhere"])


if __name__ == "__main__":
    unittest.main()
