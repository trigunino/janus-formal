from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_projector_gate import build_payload, render_markdown


class P0TracefreeHProjectorGateTests(unittest.TestCase):
    def test_projector_is_defined_but_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-projector-defined-not-source-closed",
        )
        self.assertTrue(payload["projector_defined"])
        self.assertFalse(payload["scalar_trace_selects_qtf"])
        self.assertFalse(payload["scalar_determinant_is_full_source"])
        self.assertFalse(payload["b4vol_is_full_source"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_component_count_is_trace_free_rank_nine(self) -> None:
        count = build_payload()["component_count"]

        self.assertEqual(count["symmetric_h_components"], 10)
        self.assertEqual(count["determinant_trace_rank"], 1)
        self.assertEqual(count["tracefree_h_rank"], 9)

    def test_projector_formulas_and_trace_tests_are_recorded(self) -> None:
        payload = build_payload()
        trace_tests = " ".join(payload["trace_tests"])

        self.assertEqual(payload["linearized_identity_branch"], "P_TF(S)=S-(Tr(S)/4)I")
        self.assertEqual(payload["covariant_h_branch"], "P_TF(N)=N-(Tr(H^{-1}N)/4)H")
        self.assertIn("Tr(P_TF(S))=0", trace_tests)
        self.assertIn("Tr(H^{-1}P_TF(N))=0", trace_tests)

    def test_determinant_and_b4vol_are_rejected_as_full_sources(self) -> None:
        payload = build_payload()
        rejected = " ".join(payload["rejected_full_sources"])
        guardrails = " ".join(payload["guardrails"])

        self.assertIn("Tr(H^{-1} delta H)", payload["determinant_trace_identity"])
        self.assertIn("rank 9", payload["qtf_channel"])
        self.assertFalse(payload["scalar_trace_selects_qtf"])
        self.assertIn("scalar determinant", rejected)
        self.assertIn("B4vol", rejected)
        self.assertIn("Q_TF selector", guardrails)

    def test_markdown_reports_projector_and_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Projector", markdown)
        self.assertIn("P_TF(S)=S-(Tr(S)/4)I", markdown)
        self.assertIn("P_TF(N)=N-(Tr(H^{-1}N)/4)H", markdown)
        self.assertIn("tracefree_h_rank", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Remaining lock", markdown)


if __name__ == "__main__":
    unittest.main()
