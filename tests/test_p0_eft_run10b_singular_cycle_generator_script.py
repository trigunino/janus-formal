from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_singular_cycle_generator import build_payload, render_markdown


class P0EFTRun10BSingularCycleGeneratorTests(unittest.TestCase):
    def test_singular_cycle_generator_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_singular_cycle_generator_ready"])
        self.assertTrue(status["singular_cycle_represents_z2_generator_proved"])
        self.assertTrue(status["around_sigma_maps_to_generator"])

    def test_remaining_global_locks_stay_closed_false(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_cycle_map(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldSingularCycleGenerator", markdown)
        self.assertIn("aroundSigma -> generator", markdown)
        self.assertIn("singularCycleRepresentsZ2Generator", markdown)


if __name__ == "__main__":
    unittest.main()
