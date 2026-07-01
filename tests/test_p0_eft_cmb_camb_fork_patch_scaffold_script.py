from __future__ import annotations

import unittest
from pathlib import Path

from scripts.build_p0_eft_cmb_camb_fork_patch_scaffold import build_payload


class P0EFTCMBCAMBForkPatchScaffoldTests(unittest.TestCase):
    def test_patch_scaffold_is_written(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["patch_scaffold_written"])
        self.assertTrue(payload["fortran_hook_scaffold_written"])
        self.assertTrue(payload["python_table_hook_written"])
        for path in payload["files"].values():
            self.assertTrue(Path(path).exists())

    def test_scaffold_does_not_claim_exact_fork(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["exact_camb_fork_built"])
        self.assertFalse(payload["boltzmann_equations_modified_in_solver"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
