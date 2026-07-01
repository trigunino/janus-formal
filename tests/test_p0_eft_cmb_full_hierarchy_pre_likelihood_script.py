from __future__ import annotations

import unittest

from scripts.build_p0_eft_cmb_full_hierarchy_pre_likelihood import build_payload


class P0EFTCMBFullHierarchyPreLikelihoodTests(unittest.TestCase):
    def test_full_hierarchy_pre_likelihood_runs(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "cmb-full-hierarchy-pre-likelihood-computed")
        self.assertTrue(payload["photon_baryon_neutrino_hierarchy_integrated"])
        self.assertTrue(payload["primordial_spectrum_included"])
        self.assertTrue(payload["tt_te_ee_lensing_proxy_computed"])

    def test_planck_likelihood_stays_open(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["validated_against_external_boltzmann_code"])
        self.assertFalse(payload["uncompressed_planck_likelihood_ready"])
        self.assertFalse(payload["direct_cmb_likelihood_ready"])


if __name__ == "__main__":
    unittest.main()
