from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_ionization_equilibrium_solution import build_payload, write_reports


class P0EFTJanusZ4IonizationEquilibriumSolutionScriptTests(unittest.TestCase):
    def test_stationary_peebles_root_solves_equilibrium(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["root_residual"], "0")
        self.assertTrue(payload["peebles_stationary_equation_solved"])
        self.assertTrue(payload["positive_root_selected"])
        self.assertTrue(payload["visibility_can_use_equilibrium_root"])
        self.assertFalse(payload["full_time_dependent_ionization_solved"])
        self.assertFalse(payload["physical_recombination_visibility_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_equilibrium_solution.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_equilibrium_solution.md").exists())
        self.assertIn("time-dependent", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
