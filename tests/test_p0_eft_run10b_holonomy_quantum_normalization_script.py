from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_holonomy_quantum_normalization import (
    build_payload,
    render_markdown,
)


class P0EFTRun10BHolonomyQuantumNormalizationTests(unittest.TestCase):
    def test_normalization_interface_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_holonomy_quantum_normalization_interface_ready"])
        self.assertTrue(status["normalization_to_flux_law_arrow_formalized"])
        self.assertTrue(status["run10b_z2_holonomy_unit_interface_ready"])
        self.assertTrue(status["z2_unit_to_normalization_arrow_formalized"])

    def test_normalization_partially_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["spin_connection_gauge_fixed_on_cycle_proved"])
        self.assertTrue(status["holonomy_unit_chosen_by_orbifold_generator_proved"])
        self.assertTrue(status["flux_divided_by_holonomy_unit_well_defined"])
        self.assertTrue(status["holonomy_quantum_normalized_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_holonomy_unit(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldZ2HolonomyUnit", markdown)
        self.assertIn("P0EFTOrbifoldGeneratorHolonomyUnit", markdown)
        self.assertIn("P0EFTOrbifoldSpinConnectionGaugeFix", markdown)
        self.assertIn("P0EFTOrbifoldHolonomyQuantumNormalized", markdown)
        self.assertIn("holonomy unit", markdown)
        self.assertIn("Z2 orbifold generator", markdown)


if __name__ == "__main__":
    unittest.main()
