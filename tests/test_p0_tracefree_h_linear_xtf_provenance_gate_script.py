from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_linear_xtf_provenance_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHLinearXtfProvenanceGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-linear-xtf-provenance-gate-open")
        self.assertFalse(payload["all_candidates_pass_gate"])
        self.assertFalse(payload["any_candidate_accepted"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_linear_xtf_requires_source_derived_covariant_stf_same_bridge(self) -> None:
        payload = build_payload()
        requirements = payload["x_tf_requirements"]

        self.assertEqual(payload["linear_coupling"], "int Q_TF^{ab} X_TF_ab")
        self.assertIn("source-derived covariant STF rank-2 same-bridge", payload["acceptance_rule"])
        self.assertTrue(requirements["source_derived"])
        self.assertTrue(requirements["covariant"])
        self.assertTrue(requirements["stf"])
        self.assertTrue(requirements["rank_2"])
        self.assertTrue(requirements["same_bridge"])
        self.assertTrue(requirements["dependency_terms_included_if_present"])

    def test_requested_candidates_are_present_and_blocked(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["candidates"]}

        self.assertIn("Janus coupled stress STF", rows)
        self.assertIn("Pi_TF", rows)
        self.assertIn("Weyl/shear", rows)
        self.assertIn("Vlasov quadrupole", rows)
        self.assertIn("Phi_Sigma/N_alpha", rows)
        self.assertIn("BF/GL multiplier", rows)
        self.assertFalse(any(row["source_derived_covariant_stf_rank2_same_bridge"] for row in rows.values()))
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertIn("M15/M30", rows["Janus coupled stress STF"]["blocker"])
        self.assertIn("matter variation", rows["Pi_TF"]["blocker"])
        self.assertIn("congruence lift", rows["Pi_TF"]["blocker"])
        self.assertIn("diagnostic", rows["Weyl/shear"]["blocker"])
        self.assertIn("field equation", rows["Weyl/shear"]["blocker"])
        self.assertIn("Vlasov moment hierarchy", rows["Vlasov quadrupole"]["blocker"])
        self.assertIn("Janus action/source", rows["Phi_Sigma/N_alpha"]["blocker"])
        self.assertIn("constraint action", rows["BF/GL multiplier"]["blocker"])

    def test_dependency_terms_are_included_for_h_l_phi_and_matter(self) -> None:
        payload = build_payload()
        terms = {row["dependency"]: row for row in payload["dependency_terms"]}

        self.assertFalse(payload["xtf_dependencies_can_be_ignored"])
        self.assertEqual(set(terms), {"H", "L", "phi", "matter"})
        self.assertIn("delta H", terms["H"]["term"])
        self.assertIn("delta L", terms["L"]["term"])
        self.assertIn("delta phi", terms["phi"]["term"])
        self.assertIn("delta_matter X_TF", terms["matter"]["term"])
        self.assertIn("H, L, phi, and matter", payload["variation_rule"])

    def test_residual_scalars_and_determinant_trace_are_rejected(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rejected_routes"]}
        guardrails = " ".join(payload["guardrails"])

        self.assertFalse(payload["residual_xtf_allowed"])
        self.assertFalse(payload["scalars_allowed"])
        self.assertFalse(payload["determinant_trace_allowed"])
        self.assertFalse(rows["residual_X_TF"]["accepted"])
        self.assertFalse(rows["scalars"]["accepted"])
        self.assertFalse(rows["determinant_trace"]["accepted"])
        self.assertIn("source-derived", rows["residual_X_TF"]["reason"])
        self.assertIn("STF rank-2", rows["scalars"]["reason"])
        self.assertIn("trace/volume", rows["determinant_trace"]["reason"])
        self.assertIn("residual X_TF", guardrails)

    def test_markdown_reports_prediction_false_and_dependency_gate(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Linear X_TF Provenance Gate", markdown)
        self.assertIn("Linear coupling: `int Q_TF^{ab} X_TF_ab`", markdown)
        self.assertIn("Janus coupled stress STF", markdown)
        self.assertIn("Pi_TF", markdown)
        self.assertIn("Weyl/shear", markdown)
        self.assertIn("BF/GL multiplier", markdown)
        self.assertIn("Dependency Terms", markdown)
        self.assertIn("Residual X_TF allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
