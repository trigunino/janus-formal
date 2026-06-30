from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_integer_flux_law import build_payload, render_markdown


class P0EFTRun10BIntegerFluxLawTests(unittest.TestCase):
    def test_integer_flux_law_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_integer_flux_law_ready"])
        self.assertTrue(status["integer_flux_law_proved"])
        self.assertTrue(status["z2_holonomy_period_integer"])

    def test_orientation_remains_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertFalse(status["janus_orientation_rule_proved"])
        self.assertFalse(status["orbifold_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_integer_flux_law(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldIntegerFluxLaw", markdown)
        self.assertIn("integerFluxLawDerived", markdown)
        self.assertIn("integerFluxDataClosed", markdown)


if __name__ == "__main__":
    unittest.main()
