from __future__ import annotations

import unittest

from scripts.build_p0_eft_primordial_coupled_cmb_sector_scaffold import build_payload


class P0EFTPrimordialCoupledCMBSectorScaffoldTests(unittest.TestCase):
    def test_camb_hooks_are_tied_to_one_mode(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "primordial-coupled-cmb-sector-scaffold-recorded")
        self.assertTrue(payload["has_single_primordial_mode"])
        self.assertTrue(payload["sound_speed_tied_to_mode"])
        self.assertTrue(payload["opacity_lowE_tied_to_mode"])
        self.assertTrue(payload["background_geff_tied_to_mode"])
        self.assertTrue(payload["immirzi_perturbations_tied_to_mode"])
        self.assertTrue(payload["scaffold_ready"])

    def test_scaffold_is_neutral_until_derived(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["all_amplitudes_neutral"])
        self.assertFalse(payload["derived_geometry_ready"])
        self.assertFalse(payload["full_cosmology_prediction_ready_no_fit"])


if __name__ == "__main__":
    unittest.main()
