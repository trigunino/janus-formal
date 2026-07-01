from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_weyl_transfer_integration import build_payload


class P0EFTCMBWeylTransferIntegrationTests(unittest.TestCase):
    def test_weyl_transfer_integration_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-weyl-transfer-integrated-with-source-equation")
        self.assertTrue(payload["weyl_source_equation_used"])
        self.assertTrue(payload["cl_proxy_computed"])

    def test_likelihood_stays_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["visibility_is_still_proxy"])
        self.assertTrue(payload["boltzmann_hierarchy_is_still_proxy"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
