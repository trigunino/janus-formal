from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_background_action_derivation import build_payload, write_reports


class P0EFTJanusZ4BackgroundActionDerivationScriptTests(unittest.TestCase):
    def test_background_coefficients_are_action_normalized(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["friedmann_coefficient"], "8*pi*G/3")
        self.assertEqual(payload["friedmann_residual"], "0")
        self.assertEqual(payload["bianchi_residual"], "0")
        self.assertTrue(payload["background_action_derived_ready"])
        self.assertTrue(payload["full_z4_background_system_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_action_derivation.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_action_derivation.md").exists())
        self.assertIn("Einstein-Palatini", payload["scope"])


if __name__ == "__main__":
    unittest.main()
