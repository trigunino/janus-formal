from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_minimal_boltzmann_hierarchy import build_payload


class P0EFTCMBMinimalBoltzmannHierarchyTests(unittest.TestCase):
    def test_minimal_hierarchy_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-minimal-boltzmann-hierarchy-integrated")
        self.assertTrue(payload["minimal_boltzmann_hierarchy_integrated"])
        self.assertTrue(payload["cl_proxy_computed"])

    def test_full_likelihood_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["full_boltzmann_hierarchy_validated"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
