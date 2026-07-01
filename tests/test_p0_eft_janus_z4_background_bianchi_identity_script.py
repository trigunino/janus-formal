from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_background_bianchi_identity import build_payload, write_reports


class P0EFTJanusZ4BackgroundBianchiIdentityScriptTests(unittest.TestCase):
    def test_bianchi_identity_recovers_raychaudhuri(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["residual"], "0")
        self.assertTrue(payload["background_bianchi_identity_ready"])
        self.assertTrue(payload["no_extra_background_fluid_introduced"])
        self.assertFalse(payload["coefficients_from_full_action"])
        self.assertFalse(payload["full_z4_background_system_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_bianchi_identity.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_background_bianchi_identity.md").exists())
        self.assertIn("nonlinear Z4 action", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
