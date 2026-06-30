from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_projector_variation_dependency_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHProjectorVariationDependencyGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["status"],
            "tracefree-h-projector-variation-dependency-gate-open",
        )
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertFalse(payload["projector_dependency_closed"])
        self.assertFalse(payload["fixed_projector_branch_proved"])
        self.assertTrue(payload["chain_rule_requires_delta_projector"])
        self.assertEqual(payload["branches_accepted"], 0)
        self.assertFalse(payload["accepted_as_closure"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_required_variation_branches_are_recorded(self) -> None:
        rows = {row["branch"]: row for row in build_payload()["branches"]}

        self.assertEqual(len(rows), 4)
        self.assertIn("P_STF(delta X)", rows["fixed_background_projector"]["variation_rule"])
        self.assertIn("H^-1 deltaH H^-1", rows["covariant_h_projector"]["variation_rule"])
        self.assertIn("delta u", rows["screen_projector"]["variation_rule"])
        self.assertIn("(delta P_STF)[Y]", rows["chain_rule_with_projector"]["variation_rule"])
        self.assertFalse(any(row["accepted"] for row in rows.values()))

    def test_requirements_keep_gauge_tetrad_and_same_bridge(self) -> None:
        text = " ".join(build_payload()["requirements"])

        self.assertIn("fixed-background or covariant-H", text)
        self.assertIn("deltaH inverse terms", text)
        self.assertIn("delta h and delta u", text)
        self.assertIn("same L/Omega/tetrad", text)
        self.assertIn("gauge/boundary", text)

    def test_forbidden_routes_block_dropping_terms(self) -> None:
        payload = build_payload()
        text = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["residual_target_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertIn("drop delta P_STF", text)
        self.assertIn("determinant trace", text)
        self.assertIn("residual source", text)

    def test_markdown_reports_projector_dependency(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Projector Variation Dependency", markdown)
        self.assertIn("delta(P_STF Y)=P_STF(delta Y)+(delta P_STF)[Y]", markdown)
        self.assertIn("Branches accepted: 0/4", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
