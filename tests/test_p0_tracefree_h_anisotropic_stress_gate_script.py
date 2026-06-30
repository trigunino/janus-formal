from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_anisotropic_stress_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHAnisotropicStressGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-anisotropic-stress-gate-open")
        self.assertTrue(payload["pi_tf_defined"])
        self.assertTrue(payload["pi_tf_requires_congruence_u"])
        self.assertFalse(payload["pi_tf_selects_full_h_tf"])
        self.assertFalse(payload["dust_or_perfect_fluid_closes_qtf"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["prediction_ready"])

    def test_rank_counts_show_spatial_pi_is_not_full_4d_h_tf(self) -> None:
        ranks = build_payload()["rank_counts"]

        self.assertEqual(ranks["spatial_stf_pi_rank_after_u_choice"], 5)
        self.assertEqual(ranks["full_4d_h_tracefree_rank"], 9)
        self.assertEqual(ranks["unselected_4d_components_if_only_pi_spatial"], 4)

    def test_pressure_and_dust_do_not_close_qtf(self) -> None:
        rows = {row["object"]: row for row in build_payload()["rows"]}

        self.assertFalse(rows["pressure"]["closes_qtf"])
        self.assertEqual(rows["anisotropic_stress"]["closes_qtf"], "partial")
        self.assertFalse(rows["dust_or_perfect_fluid"]["closes_qtf"])

    def test_markdown_reports_required_source_and_same_l(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Anisotropic Stress", markdown)
        self.assertIn("Pi_TF selects full H_TF: False", markdown)
        self.assertIn("Needs same-L transport: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
