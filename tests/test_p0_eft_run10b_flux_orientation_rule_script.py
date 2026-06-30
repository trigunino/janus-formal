from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_flux_orientation_rule import build_payload, render_markdown


class P0EFTRun10BFluxOrientationRuleTests(unittest.TestCase):
    def test_orientation_interface_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_orientation_rule_interface_ready"])
        self.assertTrue(status["orientation_to_branch_selection_arrow_formalized"])

    def test_orientation_is_closed(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["janus_orientation_rule_proved"])
        self.assertTrue(status["integer_flux_law_proved"])
        self.assertTrue(status["orbifold_global_theorem_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_multiplicities(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldJanusOrientationRule", markdown)
        self.assertIn("multiplicity two", markdown)
        self.assertIn("multiplicity one", markdown)


if __name__ == "__main__":
    unittest.main()
