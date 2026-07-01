from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_weyl_lensing_source_target import build_payload, write_reports


class P0EFTJanusZ4WeylLensingSourceTargetScriptTests(unittest.TestCase):
    def test_weyl_lensing_target_is_declared_not_physical(self) -> None:
        payload = build_payload()
        self.assertTrue(payload["weyl_lensing_target_ready"])
        self.assertFalse(payload["weyl_lensing_physical_ready"])
        self.assertIn("Phi", payload["weyl_potential"])
        self.assertIn("Psi", payload["finite_transfer_target"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_source_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_source_target.md").exists())
        self.assertIn("Z4 scalar closure", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
