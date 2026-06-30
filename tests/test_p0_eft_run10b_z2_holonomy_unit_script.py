from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_z2_holonomy_unit import build_payload, render_markdown


class P0EFTRun10BZ2HolonomyUnitTests(unittest.TestCase):
    def test_z2_unit_interface_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_z2_holonomy_unit_interface_ready"])
        self.assertTrue(status["z2_unit_to_normalization_arrow_formalized"])
        self.assertTrue(status["z2_generator_order_two_proved"])
        self.assertTrue(status["generator_square_transported_to_orbifold"])

    def test_cycle_and_unit_are_closed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["singular_cycle_represents_z2_generator_proved"])
        self.assertTrue(status["around_sigma_maps_to_generator"])
        self.assertTrue(status["holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertTrue(status["z2_holonomy_unit_closed"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_z2_generator(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldZ2GroupLaw", markdown)
        self.assertIn("P0EFTOrbifoldSingularCycleGenerator", markdown)
        self.assertIn("P0EFTOrbifoldGeneratorHolonomyUnit", markdown)
        self.assertIn("Z2 orbifold generator", markdown)
        self.assertIn("order two", markdown)


if __name__ == "__main__":
    unittest.main()
