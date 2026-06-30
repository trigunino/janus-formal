from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_holonomy_quantum_normalized import build_payload, render_markdown


class P0EFTRun10BHolonomyQuantumNormalizedTests(unittest.TestCase):
    def test_holonomy_quantum_normalized_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_holonomy_quantum_normalized_ready"])
        self.assertTrue(status["holonomy_quantum_normalized_proved"])
        self.assertTrue(status["flux_divided_by_holonomy_unit_well_defined"])

    def test_integrality_remains_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["normalized_flux_integer_proved"])
        self.assertFalse(status["integer_flux_law_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_normalization(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldHolonomyQuantumNormalized", markdown)
        self.assertIn("flux divided by the Z2 generator holonomy unit", markdown)
        self.assertIn("holonomyQuantumNormalizedDerived", markdown)


if __name__ == "__main__":
    unittest.main()
