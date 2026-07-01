from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_camb_backend_smoke import build_payload


class P0EFTCMBBackendSmokeTests(unittest.TestCase):
    def test_camb_backend_runs_when_available(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(payload["python_camb_available"])
        self.assertTrue(payload["backend_solver_run"])
        self.assertTrue(payload["janus_background_parameters_injected"])
        self.assertFalse(payload["janus_modified_gravity_tables_injected"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])

    def test_cls_csv_is_written(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(Path(payload["camb_run"]["cls_csv"]).exists())
        self.assertEqual(payload["camb_run"]["Delta_Neff_Holst"], 0.6964238)


if __name__ == "__main__":
    unittest.main()
