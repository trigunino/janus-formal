from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_action_measure_variation_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHActionMeasureVariationGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-action-measure-variation-gate-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertFalse(payload["measure_variation_closed"])
        self.assertFalse(payload["fixed_measure_branch_proved"])
        self.assertFalse(payload["source_measure_convention_fixed"])
        self.assertIsNone(payload["source_measure_rule_accepted"])
        self.assertTrue(payload["delta_mu_terms_required"])
        self.assertFalse(payload["delta_mu_can_source_stf"])
        self.assertEqual(payload["measure_terms_accepted"], 0)
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_measure_terms_cover_fixed_metric_b4vol_and_absorbed(self) -> None:
        rows = {row["term"]: row for row in build_payload()["measure_terms"]}

        self.assertEqual(len(rows), 4)
        self.assertIn("delta_mu = 0", rows["fixed_measure"]["variation"])
        self.assertIn("Tr(H^-1 deltaH)", rows["metric_volume_measure"]["variation"])
        self.assertIn("delta log B4vol", rows["b4vol_source_measure"]["variation"])
        self.assertIn("rho_eff/X_TF", rows["effective_absorbed_measure"]["variation"])
        self.assertFalse(any(row["accepted"] for row in rows.values()))

    def test_forbidden_routes_block_trace_promotion_and_absorption(self) -> None:
        text = " ".join(build_payload()["forbidden_routes"])

        self.assertIn("drop delta_mu", text)
        self.assertIn("trace-free S_TF", text)
        self.assertIn("B4vol and dust 3-volume", text)
        self.assertIn("absorbing delta_mu into X_TF", text)

    def test_markdown_reports_measure_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Action Measure Variation", markdown)
        self.assertIn("Delta_mu terms required: True", markdown)
        self.assertIn("Delta_mu can source STF: False", markdown)
        self.assertIn("Measure terms accepted: 0/4", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
