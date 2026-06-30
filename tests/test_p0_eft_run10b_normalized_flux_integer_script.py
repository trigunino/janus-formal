from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_normalized_flux_integer import build_payload, render_markdown


class P0EFTRun10BNormalizedFluxIntegerTests(unittest.TestCase):
    def test_normalized_flux_integer_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_normalized_flux_integer_ready"])
        self.assertTrue(status["normalized_flux_integer_proved"])
        self.assertTrue(status["normalized_flux_lands_in_integer_lattice"])

    def test_global_integer_law_remains_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["integer_flux_law_proved"])
        self.assertFalse(status["orbifold_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_integer_lattice(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldNormalizedFluxInteger", markdown)
        self.assertIn("integer lattice", markdown)
        self.assertIn("normalizedFluxIntegerDerived", markdown)


if __name__ == "__main__":
    unittest.main()
