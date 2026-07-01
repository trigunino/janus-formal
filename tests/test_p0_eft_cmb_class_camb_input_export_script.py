from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_class_camb_input_export import build_payload


class P0EFTCMBClassCambInputExportTests(unittest.TestCase):
    def test_input_export_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "class-camb-input-tables-exported")
        self.assertGreater(payload["row_counts"]["background"], 10)
        self.assertTrue(Path(payload["files"]["background"]).exists())

    def test_external_solver_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["adapter_written"])
        self.assertFalse(payload["external_solver_run"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
