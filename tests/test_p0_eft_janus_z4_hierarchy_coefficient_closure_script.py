from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_hierarchy_coefficient_closure import build_payload, write_reports


class P0EFTJanusZ4HierarchyCoefficientClosureScriptTests(unittest.TestCase):
    def test_drag_and_sound_speed_coefficients_are_consistent(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["drag_energy_residual"], "0")
        self.assertTrue(payload["coefficient_scaffold_ready"])
        self.assertFalse(payload["coefficient_physical_ready"])
        self.assertIn("rho_b", payload["baryon_loading_R"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_hierarchy_coefficient_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_hierarchy_coefficient_closure.md").exists())
        self.assertIn("Z4 action", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
