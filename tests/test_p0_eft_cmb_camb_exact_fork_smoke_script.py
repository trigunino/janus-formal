from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_camb_exact_fork_smoke import build_payload


class P0EFTCMBCAMBExactForkSmokeTests(unittest.TestCase):
    def test_exact_fork_smoke_runs(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(payload["fork_dll_exists"])
        self.assertTrue(payload["fork_camb_imported"])
        self.assertTrue(payload["exact_camb_fork_built"])
        self.assertTrue(payload["boltzmann_equations_modified_in_solver"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])

    def test_exact_fork_outputs_cls(self) -> None:
        payload = build_payload(lmax=64)

        self.assertTrue(Path(payload["run"]["cls_csv"]).exists())
        self.assertGreater(payload["run"]["TT_10"], 0.0)


if __name__ == "__main__":
    unittest.main()
