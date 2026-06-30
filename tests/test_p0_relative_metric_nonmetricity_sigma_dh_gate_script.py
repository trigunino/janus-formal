from __future__ import annotations

import unittest

from scripts.build_p0_relative_metric_nonmetricity_sigma_dh_gate import (
    build_payload,
    render_markdown,
)


class P0RelativeMetricNonmetricitySigmaDHGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "relative-metric-nonmetricity-selector-open")
        self.assertTrue(payload["n_definition_closed"])
        self.assertTrue(payload["trace_tracefree_split_closed"])
        self.assertEqual(payload["trace_only_no_go"], "p0_sigma_trace_only_no_go_gate")
        self.assertEqual(payload["integrability_gate"], "p0_nonmetricity_integrability_curl_gate")
        self.assertEqual(payload["mirror_inverse_gate"], "p0_nonmetricity_mirror_inverse_gate")
        self.assertFalse(payload["source_selector_found"])
        self.assertFalse(payload["trace_only_closure_sufficient"])
        self.assertFalse(payload["prediction_ready"])

    def test_definition_and_dq_rule_are_carried(self) -> None:
        payload = build_payload()

        self.assertIn("N_alpha := D_alpha H", payload["definition"])
        self.assertIn("Sigma_alpha", payload["sigma_equivalence"])
        self.assertIn("FrechetLog_H[D_alpha H]", payload["dq_rule"])

    def test_trace_free_part_remains_required(self) -> None:
        decomp = build_payload()["decomposition"]

        self.assertIn("D_alpha log det(H)", decomp["trace"])
        self.assertIn("N_alpha_TF", decomp["trace_free"])
        self.assertIn("Q_TF", decomp["meaning"])

    def test_rejects_definition_trace_lorentz_and_fit_shortcuts(self) -> None:
        rules = " ".join(build_payload()["rejection_rules"])

        self.assertIn("do not define N_alpha and call it selected", rules)
        self.assertIn("determinant/B4vol trace", rules)
        self.assertIn("pure Lorentz Omega_alpha", rules)
        self.assertIn("do not fit N_alpha", rules)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Relative-Metric Nonmetricity", markdown)
        self.assertIn("Source selector found: False", markdown)
        self.assertIn("Trace-only closure sufficient: False", markdown)
        self.assertIn("p0_sigma_trace_only_no_go_gate", markdown)
        self.assertIn("p0_nonmetricity_integrability_curl_gate", markdown)
        self.assertIn("p0_nonmetricity_mirror_inverse_gate", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
