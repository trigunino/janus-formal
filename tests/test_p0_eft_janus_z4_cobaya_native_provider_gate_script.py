from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_cobaya_native_provider_gate import build_payload, write_reports


class P0EFTJanusZ4CobayaNativeProviderGateScriptTests(unittest.TestCase):
    def test_cobaya_can_construct_native_provider_or_reports_error(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["legacy_camb_fork_required"])
        self.assertFalse(payload["official_planck_likelihood_executed"])
        if payload["cobaya_provider_constructed"]:
            self.assertTrue(payload["provider_get_cl_ready"])
            self.assertGreaterEqual(payload["tt_length"], 1201)
        else:
            self.assertIsNotNone(payload["error"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_native_provider_gate.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_cobaya_native_provider_gate.md").exists())
        self.assertIn("cobaya_provider_constructed", payload)


if __name__ == "__main__":
    unittest.main()
