from __future__ import annotations

import unittest

from scripts.build_p0_sigma_trace_only_no_go_gate import build_payload, render_markdown


class P0SigmaTraceOnlyNoGoGateTests(unittest.TestCase):
    def test_trace_only_no_go_is_closed_but_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "trace-only-no-go-closed")
        self.assertTrue(payload["no_go_closed"])
        self.assertFalse(payload["trace_only_selects_full_sigma"])
        self.assertFalse(payload["trace_only_selects_qtf"])
        self.assertFalse(payload["prediction_ready"])

    def test_rank_count_shows_trace_free_gap(self) -> None:
        rank = build_payload()["rank_count"]

        self.assertEqual(rank["eta_symmetric_sigma_rank"], 10)
        self.assertEqual(rank["determinant_trace_rank"], 1)
        self.assertEqual(rank["trace_free_sigma_rank"], 9)

    def test_trace_identity_and_guardrails_block_qdet_absorption(self) -> None:
        payload = build_payload()
        guardrails = " ".join(payload["guardrails"])

        self.assertIn("Tr(H^{-1}D_alpha H)", payload["trace_identity"])
        self.assertIn("Q_TF", payload["missing_channel"])
        self.assertIn("do not absorb Q_TF", guardrails)
        self.assertIn("determinant closure", guardrails)

    def test_markdown_reports_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Sigma Trace-Only No-Go", markdown)
        self.assertIn("trace_free_sigma_rank", markdown)
        self.assertIn("Trace-only selects Q_TF: False", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
