from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_generator_holonomy_unit import build_payload, render_markdown


class P0EFTRun10BGeneratorHolonomyUnitTests(unittest.TestCase):
    def test_generator_holonomy_unit_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_generator_holonomy_unit_ready"])
        self.assertTrue(status["holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertTrue(status["z2_holonomy_unit_closed"])

    def test_flux_locks_remain_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["holonomy_quantum_normalized_proved"])
        self.assertFalse(status["normalized_flux_integer_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_generator_unit_map(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldGeneratorHolonomyUnit", markdown)
        self.assertIn("generator -> z2GeneratorUnit", markdown)
        self.assertIn("z2_generator_chooses_holonomy_unit", markdown)


if __name__ == "__main__":
    unittest.main()
