from __future__ import annotations

import unittest

from scripts.build_p0_eft_direct_cmb_theta_star_proxy import build_payload


class P0EFTDirectCMBThetaStarProxyTests(unittest.TestCase):
    def test_theta_star_proxy_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "direct-cmb-theta-star-proxy-computed-transfer-open")
        self.assertTrue(payload["janus_distance_ruler_proxy_ready"])
        self.assertGreater(payload["theta_star_proxy_unit"], 0.0)

    def test_no_planck_verdict_claimed(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_lcdm_compressed_planck_parameters_as_verdict"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])
        self.assertFalse(payload["is_planck_verdict"])


if __name__ == "__main__":
    unittest.main()
