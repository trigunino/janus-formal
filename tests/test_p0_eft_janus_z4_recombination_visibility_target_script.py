from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_janus_z4_recombination_visibility_target import build_payload, write_reports


class P0EFTJanusZ4RecombinationVisibilityTargetScriptTests(unittest.TestCase):
    def test_visibility_target_declares_physical_tau_dot(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["electron_density"], "n_b*x_e")
        self.assertEqual(payload["tau_dot"], "a*n_b*sigma_T*x_e")
        self.assertIn("exp(-tau)", payload["visibility"])
        self.assertTrue(payload["visibility_target_ready"])
        self.assertFalse(payload["visibility_physical_ready"])

    def test_report_writer_exports_outputs(self) -> None:
        payload = write_reports()

        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_recombination_visibility_target.json").exists())
        self.assertTrue(Path("outputs/reports/p0_eft_janus_z4_recombination_visibility_target.md").exists())
        self.assertIn("x_e", payload["next_required"])


if __name__ == "__main__":
    unittest.main()
