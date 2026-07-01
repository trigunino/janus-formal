from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_class_camb_adapter import build_payload


class P0EFTCMBClassCambAdapterTests(unittest.TestCase):
    def test_adapter_files_are_written(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "class-camb-adapter-written-external-run-open")
        self.assertTrue(payload["adapter_written"])
        self.assertTrue(Path(payload["class_ini"]).exists())
        self.assertTrue(Path(payload["camb_json"]).exists())
        self.assertTrue(Path(payload["runner_script"]).exists())

    def test_external_solver_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["external_solver_run"])
        self.assertFalse(payload["external_validation_passed"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
