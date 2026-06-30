from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_z2_group_law import build_payload, render_markdown


class P0EFTRun10BZ2GroupLawTests(unittest.TestCase):
    def test_z2_order_two_is_proved(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_z2_group_law_ready"])
        self.assertTrue(status["z2_generator_order_two_proved"])
        self.assertTrue(status["generator_square_transported_to_orbifold"])

    def test_remaining_holonomy_unit_inputs_stay_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["singular_cycle_represents_z2_generator_proved"])
        self.assertFalse(status["holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_generator_square(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("generator * generator = unit", markdown)
        self.assertIn("z2GeneratorOrderTwo", markdown)


if __name__ == "__main__":
    unittest.main()
