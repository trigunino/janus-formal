from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_line_of_sight_source_target import build_payload, write_reports


class P0EFTJanusZ4LineOfSightSourceTargetScriptTests(unittest.TestCase):
    def test_los_sources_are_declared_not_physical(self) -> None:
        payload = build_payload()
        self.assertTrue(payload["los_target_ready"])
        self.assertFalse(payload["los_physical_ready"])
        self.assertIn("Theta0", payload["sw_source"])
        self.assertIn("Psi_prime", payload["isw_source"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_line_of_sight_source_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_line_of_sight_source_target.md").exists())
        self.assertIn("Z4 hierarchy", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
