from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_physical_visibility_transfer import build_payload


class P0EFTCMBPhysicalVisibilityTransferTests(unittest.TestCase):
    def test_physical_visibility_transfer_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-transfer-physical-visibility-integrated")
        self.assertTrue(payload["weyl_source_equation_used"])
        self.assertTrue(payload["physical_visibility_used"])
        self.assertTrue(payload["cl_proxy_computed"])

    def test_boltzmann_and_likelihood_stay_open(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["boltzmann_hierarchy_is_still_proxy"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
