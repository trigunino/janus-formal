from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_camb_source_fork_patch_audit import build_payload


class P0EFTCMBCAMBSourceForkPatchAuditTests(unittest.TestCase):
    def test_source_fork_patch_is_applied(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["source_clone_present"])
        self.assertTrue(payload["fortran_hook_present"])
        self.assertTrue(payload["makefile_registered"])
        self.assertTrue(payload["equations_imports_hook"])
        self.assertTrue(payload["weyl_transfer_patched"])
        self.assertTrue(payload["lensing_source_patched"])
        self.assertTrue(payload["poisson_phi_patched"])
        self.assertTrue(payload["sound_speed_patched"])
        self.assertTrue(payload["opacity_patched"])
        self.assertTrue(payload["geff_background_patched"])
        self.assertTrue(payload["geff_screened_perturbation_patched"])
        self.assertTrue(payload["immirzi_momentum_patched"])
        self.assertTrue(payload["immirzi_slip_patched"])
        self.assertTrue(payload["primordial_mode_present"])
        self.assertTrue(payload["primordial_mode_ties_hooks"])
        self.assertTrue(payload["source_patch_applied"])

    def test_direct_cmb_stays_open_until_built(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["fork_build_attempted"])
        self.assertTrue(payload["exact_camb_fork_built"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
