from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_neutrino_hierarchy_target import build_payload, write_reports


class P0EFTJanusZ4NeutrinoHierarchyTargetScriptTests(unittest.TestCase):
    def test_neutrino_hierarchy_target_is_declared_not_physical(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["neutrino_target_ready"])
        self.assertFalse(payload["neutrino_physical_ready"])
        self.assertIn("F2_prime", payload["equations"]["quadrupole"])
        self.assertFalse(payload["checks"]["hierarchy_coefficients_derived"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_neutrino_hierarchy_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_neutrino_hierarchy_target.md").exists())
        self.assertIn("Z4 scalar closure", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
