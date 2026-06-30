from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_source_action_provenance_chain_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHSourceActionProvenanceChainGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-source-action-provenance-chain-gate-open",
        )
        self.assertFalse(payload["all_chain_steps_closed"])
        self.assertTrue(payload["all_origins_unclosed_or_conditional"])
        self.assertFalse(payload["any_origin_accepted"])
        self.assertFalse(payload["source_action_provenance_closed"])
        self.assertFalse(payload["same_bridge_source_term_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_accepted_source_requires_full_chain(self) -> None:
        payload = build_payload()
        chain = payload["accepted_s_tf_janus_requires_chain"]
        steps = [row["step"] for row in payload["chain_steps"]]

        self.assertEqual(payload["source_symbol"], "S_TF^Janus")
        self.assertEqual(payload["bridge"], "H/Q_TF")
        self.assertIn("S_Janus[H,L,phi,matter]", chain)
        self.assertIn("declared variation domain", chain)
        self.assertIn("deltaS/deltaH", chain)
        self.assertIn("P_STF projection", chain)
        self.assertIn("same bridge source term", chain)
        self.assertEqual(
            steps,
            [
                "S_Janus[H,L,phi,matter]",
                "declared variation domain",
                "deltaS/deltaH",
                "P_STF projection",
                "same bridge source term",
            ],
        )
        self.assertFalse(any(row["closed"] for row in payload["chain_steps"]))

    def test_candidate_origins_are_conditional_and_unaccepted(self) -> None:
        rows = {row["origin"]: row for row in build_payload()["candidate_origins"]}

        self.assertEqual(
            set(rows),
            {
                "published Janus field equation",
                "relative-H action",
                "matter variation/Pi_TF",
                "Vlasov kinetic action",
                "BF/GL constraint action",
            },
        )
        self.assertTrue(all(row["status"] == "conditional" for row in rows.values()))
        self.assertFalse(any(row["closed"] for row in rows.values()))
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("S_Janus", rows["published Janus field equation"]["blocker"])
        self.assertIn("P_STF", rows["relative-H action"]["blocker"])
        self.assertIn("Pi_TF", rows["matter variation/Pi_TF"]["blocker"])
        self.assertIn("kinetic action", rows["Vlasov kinetic action"]["blocker"])
        self.assertIn("constraint multiplier", rows["BF/GL constraint action"]["blocker"])

    def test_residual_source_and_determinant_trace_are_rejected(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rejected_routes"]}

        self.assertFalse(payload["residual_source_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertFalse(rows["residual_source"]["accepted"])
        self.assertFalse(rows["determinant_trace"]["accepted"])
        self.assertIn("not source-action provenance", rows["residual_source"]["reason"])
        self.assertIn("trace data", rows["determinant_trace"]["reason"])

    def test_markdown_reports_chain_origins_rejections_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source-Action Provenance Chain Gate", markdown)
        self.assertIn("S_Janus[H,L,phi,matter]", markdown)
        self.assertIn("deltaS/deltaH", markdown)
        self.assertIn("P_STF projection", markdown)
        self.assertIn("published Janus field equation", markdown)
        self.assertIn("relative-H action", markdown)
        self.assertIn("matter variation/Pi_TF", markdown)
        self.assertIn("Vlasov kinetic action", markdown)
        self.assertIn("BF/GL constraint action", markdown)
        self.assertIn("Residual source allowed: False", markdown)
        self.assertIn("Determinant trace allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
