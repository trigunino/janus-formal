from __future__ import annotations

import unittest

from scripts.build_p0_route_d_stf_operator_construction_obstruction import (
    build_payload,
    render_markdown,
)


class P0RouteDSTFOperatorConstructionObstructionTests(unittest.TestCase):
    def test_formal_stf_candidates_exist_but_none_is_accepted(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "stf-operator-construction-obstruction-open")
        self.assertEqual(payload["candidate_count"], 5)
        self.assertEqual(payload["accepted_candidate_count"], 0)
        self.assertTrue(payload["formal_stf_operators_exist"])
        self.assertFalse(payload["accepted_janus_derived_stf_operator_exists"])
        self.assertFalse(payload["source_action_provenance_closed"])
        self.assertFalse(payload["stability_requirements_closed"])
        self.assertFalse(payload["residual_operator_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertTrue(payload["escape_hatch_still_open"])
        self.assertFalse(payload["prediction_ready"])

    def test_candidates_cover_stf_operator_families(self) -> None:
        candidates = {row["candidate"] for row in build_payload()["candidates"]}

        self.assertEqual(
            candidates,
            {
                "relative_H_action",
                "bf_gl_constraint_action",
                "vlasov_quadrupole_moment",
                "matter_pi_tf_variation",
                "curvature_stf_operator",
            },
        )

    def test_markdown_reports_missing_chain(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("STF Operator Construction Obstruction", markdown)
        self.assertIn("Missing Chain", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
