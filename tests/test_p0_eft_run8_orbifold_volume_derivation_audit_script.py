from __future__ import annotations

import unittest

from scripts.build_p0_eft_run8_orbifold_volume_derivation_audit import build_payload, render_markdown


class P0EFTRun8OrbifoldVolumeDerivationAuditTests(unittest.TestCase):
    def test_run8_freezes_aps_and_numeric(self) -> None:
        frozen = build_payload()["frozen_sectors"]

        self.assertEqual(frozen["run7_aps_pin_spectral_axis"], "untouched")
        self.assertEqual(frozen["numeric_solver"], "untouched")

    def test_orbifold_ratio_is_closed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run8_orbifold_volume_interface_ready"])
        self.assertTrue(status["run8_euler_cover_interface_ready"])
        self.assertTrue(status["multiplicity_to_ratio_arrow_formalized"])
        self.assertTrue(status["run8_holonomy_flux_interface_ready"])
        self.assertTrue(status["flux_to_branch_index_arrow_formalized"])
        self.assertTrue(status["flux_quantization_proved"])
        self.assertTrue(status["euler_surface_class_computed"])
        self.assertTrue(status["sheet_multiplicity_two_to_one_proved"])
        self.assertTrue(status["orbifold_cover_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_target_ratio(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("M5 / Z2", markdown)
        self.assertIn("P0EFTOrbifoldEulerCharacteristic", markdown)
        self.assertIn("P0EFTOrbifoldHolonomyFluxQuantization", markdown)
        self.assertIn("P0EFTOrbifoldJanusOrientationRule", markdown)
        self.assertIn("Vol_+:Vol_-=2:1", markdown)


if __name__ == "__main__":
    unittest.main()
