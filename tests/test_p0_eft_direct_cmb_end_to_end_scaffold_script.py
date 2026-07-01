from __future__ import annotations

import unittest

from scripts.build_p0_eft_direct_cmb_end_to_end_scaffold import build_payload


class P0EFTDirectCMBEndToEndScaffoldTests(unittest.TestCase):
    def test_end_to_end_proxy_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "direct-cmb-end-to-end-proxy-computed-not-planck-likelihood")
        self.assertTrue(payload["weyl_source_proxy_ready"])
        self.assertTrue(payload["visibility_proxy_ready"])
        self.assertTrue(payload["boltzmann_proxy_integrated"])
        self.assertTrue(payload["cl_proxy_computed"])

    def test_no_planck_likelihood_claimed(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_lcdm_compressed_planck_parameters_as_verdict"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])
        self.assertFalse(payload["is_planck_verdict"])


if __name__ == "__main__":
    unittest.main()
