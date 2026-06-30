from __future__ import annotations

import unittest

from scripts.build_p0_lapse_slice_from_janus_gauge_probe import build_payload, render_markdown


class P0LapseSliceFromJanusGaugeProbeTests(unittest.TestCase):
    def test_field_equations_do_not_fix_general_lapse_slice(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "lapse-slice-gauge-derivation-conditional")
        self.assertFalse(payload["janus_field_equations_fix_lapse_slice"])
        self.assertFalse(payload["general_perturbed_branch_lapse_slice_fixed"])
        self.assertFalse(payload["j_phi_selected_without_slice_data"])
        self.assertFalse(payload["prediction_ready"])

    def test_restricted_branches_can_fix_lapse_or_slice(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["proper_time_slicing_can_fix_lapse"])
        self.assertTrue(payload["flrw_comoving_branch_can_fix_lapse_slice"])
        self.assertTrue(payload["new_gauge_axiom_risk"])

    def test_rows_distinguish_source_weight_from_gauge(self) -> None:
        rows = {row["condition"]: row for row in build_payload()["rows"]}

        self.assertTrue(rows["m15_b4vol_source_weight"]["source_equation_only"])
        self.assertFalse(rows["m15_b4vol_source_weight"]["fixes_lapse_ratio"])
        self.assertFalse(rows["proper_time_comoving_both_sectors"]["source_equation_only"])
        self.assertTrue(rows["proper_time_comoving_both_sectors"]["fixes_lapse_ratio"])

    def test_no_observational_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_keeps_general_branch_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Janus field equations fix lapse/slice: False", markdown)
        self.assertIn("General perturbed branch lapse/slice fixed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
