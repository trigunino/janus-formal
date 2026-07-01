from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_scalar_conservation_identity import build_payload, write_reports


class P0EFTJanusZ4ScalarConservationIdentityScriptTests(unittest.TestCase):
    def test_scalar_conservation_has_no_single_sector_residual(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["single_sector_continuity_residual"], "0")
        self.assertEqual(payload["single_sector_euler_residual"], "0")
        self.assertTrue(payload["scalar_conservation_identity_ready"])
        self.assertTrue(payload["no_fictitious_cross_metric_force"])
        self.assertFalse(payload["full_z4_scalar_perturbations_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_conservation_identity.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_scalar_conservation_identity.md").exists())
        self.assertIn("full Z4 action", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
