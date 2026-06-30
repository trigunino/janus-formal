from __future__ import annotations

import unittest

from scripts.build_p0_route_d_source_derived_stf_operator_escape_gate import (
    build_payload,
    render_markdown,
)


class P0RouteDSourceDerivedSTFOperatorEscapeGateTests(unittest.TestCase):
    def test_only_open_escape_is_source_derived_stf_operator(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-derived-stf-operator-escape-open")
        self.assertTrue(payload["source_free_pde_excluded"])
        self.assertEqual(payload["only_open_escape"], "source-derived STF curvature operator")
        self.assertFalse(payload["accepted_janus_action_exists"])
        self.assertFalse(payload["accepted_operator_exists"])
        self.assertFalse(payload["stf_source_action_provenance_closed"])
        self.assertFalse(payload["same_bridge_source_term_closed"])
        self.assertFalse(payload["residual_operator_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_chain_mentions_action_variation_stf_same_l_and_stability(self) -> None:
        chain = " ".join(build_payload()["required_chain"])

        self.assertIn("Janus action", chain)
        self.assertIn("deltaS", chain)
        self.assertIn("P_STF", chain)
        self.assertIn("same-L", chain)
        self.assertIn("stability", chain)

    def test_markdown_reports_escape_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("STF Operator Escape Gate", markdown)
        self.assertIn("Accepted operator exists: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
