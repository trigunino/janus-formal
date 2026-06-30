from __future__ import annotations

import unittest

from scripts.build_p0_b_jphi_qdet_conditional_selection import build_payload


class P0BJphiQdetConditionalSelectionTests(unittest.TestCase):
    def test_selects_4volume_conditionally_not_predictively(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "conditional-selection-open")
        self.assertEqual(payload["selected_field_residual_branch"], "field_equation_4volume_source")
        self.assertFalse(payload["source_traceability_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_selection_keeps_dust_flux_auxiliary_and_rho_eff_single_count(self) -> None:
        rules = " ".join(row["selected"] + row["reason"] for row in build_payload()["selection_rule"])

        self.assertIn("field_equation_4volume_source", rules)
        self.assertIn("dust_flux_3volume_auxiliary_only", rules)
        self.assertIn("rho_eff_allowed_after_B_absorption", rules)
        self.assertIn("Q_det must not be multiplied again", rules)

    def test_consequences_keep_qcross_and_lapse_separate(self) -> None:
        consequences = " ".join(build_payload()["consequences"])

        self.assertIn("Q_det", consequences)
        self.assertIn("Q_cross remains optical", consequences)
        self.assertIn("lapse terms stay present", consequences)
        self.assertIn("D_receiver", consequences)


if __name__ == "__main__":
    unittest.main()
