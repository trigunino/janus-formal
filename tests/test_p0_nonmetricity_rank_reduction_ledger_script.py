from __future__ import annotations

import unittest

from scripts.build_p0_nonmetricity_rank_reduction_ledger import (
    build_payload,
    render_markdown,
)


class P0NonmetricityRankReductionLedgerTests(unittest.TestCase):
    def test_rank_ledger_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "nonmetricity-rank-reduction-ledger-open")
        self.assertTrue(payload["algebraic_mirror_closed"])
        self.assertTrue(payload["trace_channel_insufficient"])
        self.assertFalse(payload["source_trace_free_h_selected"])
        self.assertFalse(payload["accepted_as_prediction_input"])
        self.assertFalse(payload["prediction_ready"])

    def test_rank_counts_are_explicit_for_4d(self) -> None:
        ranks = build_payload()["rank_counts"]

        self.assertEqual(ranks["symmetric_H_components"], 10)
        self.assertEqual(ranks["N_alpha_one_form_components_before_integrability"], 40)
        self.assertEqual(ranks["trace_N_one_form_components"], 4)
        self.assertEqual(ranks["trace_free_N_one_form_components_before_integrability"], 36)
        self.assertEqual(ranks["H_potential_components_after_integrability"], 10)
        self.assertEqual(ranks["trace_free_H_components_after_trace_split"], 9)

    def test_gate_rows_show_what_is_closed_and_open(self) -> None:
        rows = {row["gate"]: row for row in build_payload()["rows"]}

        self.assertTrue(rows["definition"]["closed"])
        self.assertTrue(rows["trace_only_no_go"]["closed"])
        self.assertTrue(rows["tracefree_projector"]["closed"])
        self.assertTrue(rows["tracefree_source_candidates"]["closed"])
        self.assertTrue(rows["isotropy_no_go"]["closed"])
        self.assertFalse(rows["curl_integrability"]["closed"])
        self.assertTrue(rows["mirror_inverse"]["closed"])
        self.assertFalse(rows["source_acceptance"]["closed"])

    def test_markdown_reports_remaining_trace_free_source_problem(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Nonmetricity Rank Reduction", markdown)
        self.assertIn("trace_free_H_components_after_trace_split", markdown)
        self.assertIn("Source trace-free H selected: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
