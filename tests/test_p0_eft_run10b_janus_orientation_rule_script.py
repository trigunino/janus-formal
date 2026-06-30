from __future__ import annotations

import unittest

from scripts.build_p0_eft_run10b_janus_orientation_rule import build_payload, render_markdown


class P0EFTRun10BJanusOrientationRuleTests(unittest.TestCase):
    def test_janus_orientation_rule_ready(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["run10b_janus_orientation_rule_ready"])
        self.assertTrue(status["janus_orientation_rule_proved"])
        self.assertTrue(status["orbifold_global_theorem_proved"])

    def test_no_fit_still_waits_for_aps(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["integer_flux_law_proved"])
        self.assertFalse(status["full_cosmology_prediction_ready_no_fit"])

    def test_report_names_orientation_rule(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("P0EFTOrbifoldJanusOrientationRule", markdown)
        self.assertIn("janusOrientationRuleDerived", markdown)
        self.assertIn("orientationRuleClosed", markdown)


if __name__ == "__main__":
    unittest.main()
