from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_planck_lowl_direct_gate import build_payload


class P0EFTCMBPlanckLowLDirectGateTests(unittest.TestCase):
    def test_planck_lowl_direct_gate_runs(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["cobaya_packages_installed"])
        self.assertTrue(payload["exact_camb_fork_built"])
        self.assertTrue(payload["planck_lowl_likelihood_run"])
        self.assertTrue(payload["uncompressed_planck_lowl_used"])
        self.assertFalse(payload["uncompressed_planck_highl_used"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])

    def test_chi2_values_are_extracted(self) -> None:
        payload = build_payload()
        run = payload["run"]

        self.assertIsNotNone(run["chi2_planck_2018_lowl_TT"])
        self.assertIsNotNone(run["chi2_planck_2018_lowl_EE"])
        self.assertIsNotNone(run["chi2_CMB"])
        self.assertGreater(run["chi2_CMB"], 0.0)


if __name__ == "__main__":
    unittest.main()
