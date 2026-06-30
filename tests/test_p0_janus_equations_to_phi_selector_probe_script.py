from __future__ import annotations

import unittest

from scripts.build_p0_janus_equations_to_phi_selector_probe import build_payload, render_markdown


class P0JanusEquationsToPhiSelectorProbeTests(unittest.TestCase):
    def test_janus_equations_select_b4vol_not_phi(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "janus-equations-fix-b4vol-not-phi-without-extra-gauge",
        )
        self.assertTrue(payload["janus_equations_select_b4vol_weight"])
        self.assertFalse(payload["janus_equations_select_phi_without_extra_gauge"])
        self.assertFalse(payload["source_derived_phi_selector_found"])
        self.assertFalse(payload["prediction_ready"])

    def test_extra_gauge_can_select_but_is_not_sourced(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["extra_unit_lapse_slice_gauge_selects_phi"])
        self.assertTrue(payload["extra_identity_background_selects_epsilon_zero"])
        self.assertFalse(payload["extra_gauge_source_supplied"])
        self.assertEqual(payload["lapse_slice_probe_status"], "lapse-slice-gauge-derivation-conditional")
        self.assertTrue(payload["proper_time_slicing_can_fix_lapse"])
        self.assertTrue(payload["flrw_comoving_branch_can_fix_lapse_slice"])
        self.assertFalse(payload["general_perturbed_branch_lapse_slice_fixed"])
        self.assertFalse(payload["physics_closed"])

    def test_selector_rows_distinguish_m15_from_extra_gauge(self) -> None:
        rows = {row["row"]: row for row in build_payload()["selectors"]}

        self.assertFalse(rows["m15_cross_source_weight"]["fixes_phi"])
        self.assertFalse(rows["decomposition_with_free_lapse_slice"]["fixes_phi"])
        self.assertTrue(rows["extra_unit_lapse_slice_gauge"]["fixes_phi"])
        self.assertTrue(rows["extra_identity_background"]["fixes_phi"])

    def test_no_observational_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_keeps_selector_gap_visible(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Janus equations select B4vol weight: True", markdown)
        self.assertIn("Janus equations select phi without extra gauge: False", markdown)
        self.assertIn("General perturbed branch lapse/slice fixed: False", markdown)
        self.assertIn("Source-derived phi selector found: False", markdown)


if __name__ == "__main__":
    unittest.main()
