from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_ionization_ode_solver_target import build_payload, write_reports


class P0EFTJanusZ4IonizationODESolverTargetScriptTests(unittest.TestCase):
    def test_ode_solver_produces_bounded_history(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["bounded_ionization_history_produced"])
        self.assertTrue(payload["visibility_built_from_history"])
        self.assertTrue(payload["z4_expansion_rate_inserted"])
        self.assertGreaterEqual(payload["x_e_min"], 0.0)
        self.assertLessEqual(payload["x_e_max"], 1.0)
        self.assertFalse(payload["calibrated_recombination_coefficients_used"])
        self.assertFalse(payload["physical_recombination_visibility_nonproxy"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_ode_solver_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_ode_solver_target.md").exists())
        self.assertIn("LOS", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
