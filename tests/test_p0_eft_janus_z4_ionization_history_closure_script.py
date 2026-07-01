from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_ionization_history_closure import build_payload, write_reports


class P0EFTJanusZ4IonizationHistoryClosureScriptTests(unittest.TestCase):
    def test_ionization_history_equations_are_targets_not_solutions(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["ionization_scaffold_ready"])
        self.assertFalse(payload["ionization_physical_ready"])
        self.assertFalse(payload["checks"]["ionization_history_solved"])
        self.assertIn("x_e", payload["peebles_rhs"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_history_closure.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_ionization_history_closure.md").exists())
        self.assertIn("H_Z4", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
