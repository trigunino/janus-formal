from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_planck_full_direct_gate import build_payload


class P0EFTCMBPlanckFullDirectGateTests(unittest.TestCase):
    def test_full_planck_direct_gate_runs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["cobaya_packages_installed"])
        self.assertTrue(payload["exact_camb_fork_built"])
        self.assertTrue(payload["full_planck_likelihood_run"])
        self.assertTrue(payload["uncompressed_planck_highl_used"])
        self.assertTrue(payload["uncompressed_planck_lowl_used"])
        self.assertTrue(payload["uncompressed_planck_lensing_used"])
        self.assertTrue(payload["direct_cmb_likelihood_ready"])

    def test_fixed_branch_is_rejected_by_full_planck(self) -> None:
        payload = build_payload()
        run = payload["run"]

        self.assertIsNotNone(run["chi2_CMB"])
        self.assertGreater(run["chi2_CMB"], 2000.0)
        self.assertFalse(payload["cmb_observationally_accepted"])


if __name__ == "__main__":
    unittest.main()
