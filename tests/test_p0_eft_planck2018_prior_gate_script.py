from __future__ import annotations

import unittest

from scripts.build_p0_eft_planck2018_prior_gate import build_payload, read_priors


class P0EFTPlanck2018PriorGateTests(unittest.TestCase):
    def test_planck_priors_load(self) -> None:
        priors = read_priors()

        self.assertIn("Omega_m", priors)
        self.assertGreater(priors["Omega_m"]["sigma"], 0.0)

    def test_holst_branch_omega_m_is_scored(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "planck2018-lcdm-derived-omega-m-stress-test-computed")
        self.assertGreater(payload["Omega_m_chi2"], 0.0)
        self.assertFalse(payload["is_direct_janus_cmb_likelihood"])
        self.assertFalse(payload["planck_full_likelihood_computed"])


if __name__ == "__main__":
    unittest.main()
