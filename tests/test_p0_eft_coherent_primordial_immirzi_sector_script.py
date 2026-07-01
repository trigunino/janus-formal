from __future__ import annotations

import unittest

from scripts.build_p0_eft_coherent_primordial_immirzi_sector import build_payload


class P0EFTCoherentPrimordialImmirziSectorTests(unittest.TestCase):
    def test_unique_coefficients_are_derived(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "coherent-primordial-immirzi-sector-derived-contract")
        self.assertTrue(payload["unique_coefficients_derived"])
        self.assertEqual(payload["coefficients"], {"c_pi": 0.0, "c_q": 1.0, "c_slip": 1.0})

    def test_contract_ready_but_not_planck_claimed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["camb_patch_contract_ready"])
        self.assertIn("c_coherent_immirzi", payload["camb_single_hook"])
        self.assertFalse(payload["camb_patch_activated"])
        self.assertFalse(payload["planck_accepted"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
