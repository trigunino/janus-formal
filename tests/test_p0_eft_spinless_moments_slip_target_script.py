from __future__ import annotations

import unittest

from scripts.build_p0_eft_spinless_moments_slip_target import build_payload, render_markdown


class P0EFTSpinlessMomentsSlipTargetTests(unittest.TestCase):
    def test_spinless_moments_structured_but_slip_open(self) -> None:
        status = build_payload()["theorem_status"]

        self.assertTrue(status["spinless_moment0_density_written"])
        self.assertTrue(status["spinless_continuity_conditionally_closed"])
        self.assertTrue(status["pressure_pi_moments_defined"])
        self.assertFalse(status["slip_formula_derived_from_field_equations"])
        self.assertFalse(status["lensing_growth_sources_closed"])

    def test_pi_is_not_assumed_zero(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["theorem_status"]["pi_isotropy_not_assumed"])
        self.assertIn("not automatic", payload["moments"]["moment2_pressure_pi"])

    def test_slip_target_contains_run1_substitution(self) -> None:
        slip = build_payload()["slip"]

        self.assertIn("beta*Delta_chi", slip["target_formula"])
        self.assertIn("lambda=-4*q_T", slip["after_run1_substitution"])

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("slip_formula_derived_from_field_equations: False", markdown)
        self.assertIn("prediction_ready_unconditional: False", markdown)


if __name__ == "__main__":
    unittest.main()
