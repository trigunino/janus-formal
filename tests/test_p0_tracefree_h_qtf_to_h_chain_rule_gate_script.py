from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_qtf_to_h_chain_rule_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHQtfToHChainRuleGateTests(unittest.TestCase):
    def test_gate_is_open_formal_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-qtf-to-h-chain-rule-gate-open")
        self.assertEqual(payload["target_channel"], "H_TF/Q_TF")
        self.assertTrue(payload["chain_rule_formal"])
        self.assertFalse(payload["source_provenance_closed"])
        self.assertFalse(payload["projector_variation_dependency_ready"])
        self.assertFalse(payload["frechet_log_adjoint_ready"])
        self.assertFalse(payload["qtf_to_h_variation_ready"])
        self.assertFalse(payload["accepted_as_closure"])
        self.assertEqual(payload["accepted_branches"], [])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_rule_formulas_are_recorded(self) -> None:
        rows = {row["step"]: row for row in build_payload()["chain_steps"]}

        self.assertIn("Q = 1/2 Log(H)", rows["regular_log_branch"]["formula"])
        self.assertIn("FrechetLog_H[delta H]", rows["frechet_variation"]["formula"])
        self.assertIn("P_STF", rows["stf_projection"]["formula"])
        self.assertIn("FrechetLog_H^*", rows["adjoint_pullback"]["formula"])
        self.assertIn("H^{-1} delta H", rows["commuting_shortcut"]["formula"])
        self.assertFalse(any(row["accepted"] for row in rows.values()))

    def test_commuting_shortcut_is_conditional_only(self) -> None:
        payload = build_payload()
        rows = {row["step"]: row for row in payload["chain_steps"]}

        self.assertTrue(payload["commuting_shortcut_conditional"])
        self.assertFalse(payload["commuting_shortcut_unconditional_allowed"])
        self.assertIn("[H, delta H]=0", rows["commuting_shortcut"]["condition"])

    def test_requirements_keep_same_bridge_mirror_and_integrability(self) -> None:
        text = " ".join(build_payload()["requirements"])

        self.assertIn("regular log/polar branch", text)
        self.assertIn("p0_tracefree_h_projector_variation_dependency_gate", text)
        self.assertIn("p0_tracefree_h_frechet_log_adjoint_gate", text)
        self.assertIn("same H, L and Omega", text)
        self.assertIn("H_minus=H^{-1}", text)
        self.assertIn("Q_minus=-Q", text)
        self.assertIn("curl integrability", text)
        self.assertIn("Janus source/action provenance", text)

    def test_forbidden_routes_block_scalar_and_residual_shortcuts(self) -> None:
        payload = build_payload()
        text = " ".join(payload["forbidden_routes"])

        self.assertFalse(payload["residual_target_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertIn("scalar trace", text)
        self.assertIn("log det(H)", text)
        self.assertIn("residual targets", text)
        self.assertIn("projector dependency", text)
        self.assertIn("source provenance", text)

    def test_markdown_reports_chain_and_verdict(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Q_TF To H Chain Rule", markdown)
        self.assertIn("delta Q = 1/2 FrechetLog_H[delta H]", markdown)
        self.assertIn("delta S/delta H", markdown)
        self.assertIn("Projector variation dependency ready: False", markdown)
        self.assertIn("FrechetLog adjoint ready: False", markdown)
        self.assertIn("Commuting shortcut unconditional allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)
        self.assertIn("Verdict:", markdown)


if __name__ == "__main__":
    unittest.main()
