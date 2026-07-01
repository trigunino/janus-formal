from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_geometric_cmb_idea_screen import build_payload, write_reports


class P0EFTJanusZ4GeometricCMBIdeaScreenTests(unittest.TestCase):
    def test_screen_uses_fixed_geometric_choices(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "janus-z4-geometric-cmb-idea-screen")
        self.assertTrue(payload["branch_only_diagnostic"])
        self.assertFalse(payload["solver_numerics_modified"])
        self.assertFalse(payload["planck_validation_claimed"])
        self.assertFalse(payload["observational_planck_gate_passed"])
        self.assertTrue(payload["fixed_geometric_choices"]["no_continuous_fit_factor"])
        self.assertEqual(payload["fixed_geometric_choices"]["membrane_a_sigma"], "2/3")
        self.assertEqual(payload["fixed_geometric_choices"]["z4_quarter_turn"], "pi/2")
        self.assertIn("passes", payload["eb_hidden_conservation"])
        self.assertIn("passes", payload["weyl_lensing_mirror_projection"])
        self.assertIn("passes", payload["swisw_membrane_memory"])
        self.assertIsInstance(payload["recommended_next_branches"], list)

    def test_report_writer_exports_outputs(self) -> None:
        write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_geometric_cmb_idea_screen.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_geometric_cmb_idea_screen.md").exists())


if __name__ == "__main__":
    unittest.main()
