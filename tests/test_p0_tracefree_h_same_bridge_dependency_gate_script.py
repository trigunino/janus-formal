from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_same_bridge_dependency_gate import (
    build_payload,
    render_markdown,
)


class P0TracefreeHSameBridgeDependencyGateTests(unittest.TestCase):
    def test_gate_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-same-bridge-dependency-gate-open")
        self.assertFalse(payload["coupling_valid_without_same_bridge"])
        self.assertFalse(payload["source_provenance_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_coupling_requires_same_bridge_tetrad_and_congruence(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["linear_coupling"], "int Q_TF^{ab} X_TF_ab")
        self.assertTrue(payload["same_bridge_required"])
        self.assertTrue(payload["same_tetrad_required"])
        self.assertTrue(payload["same_congruence_required"])
        self.assertIn("same bridge, tetrad, and congruence", payload["same_bridge_rule"])

    def test_requested_obligations_are_listed_and_open(self) -> None:
        rows = {row["obligation"]: row for row in build_payload()["obligations"]}

        self.assertEqual(
            set(rows),
            {
                "bridge_map",
                "tetrad_L",
                "projector_congruence_u",
                "measure",
                "gauge_boundary",
                "dependency_variation",
                "source_provenance",
            },
        )
        self.assertFalse(any(row["closed"] for row in rows.values()))
        self.assertIn("same bridge branch", rows["bridge_map"]["requires"])
        self.assertIn("same tetrad/L", rows["tetrad_L"]["requires"])
        self.assertIn("congruence u", rows["projector_congruence_u"]["requires"])
        self.assertIn("integration measure", rows["measure"]["requires"])
        self.assertIn("boundary", rows["gauge_boundary"]["requires"])
        self.assertIn("delta X_TF", rows["dependency_variation"]["requires"])
        self.assertIn("accepted Janus", rows["source_provenance"]["requires"])

    def test_dependency_variation_terms_cover_h_l_phi_and_matter(self) -> None:
        payload = build_payload()
        terms = {row["dependency"]: row for row in payload["dependency_terms"]}

        self.assertTrue(payload["dependency_terms_required_if_present"])
        self.assertEqual(set(terms), {"H", "L", "phi", "matter"})
        self.assertTrue(all(row["required_if_present"] for row in terms.values()))
        self.assertIn("delta H", terms["H"]["variation_term"])
        self.assertIn("delta L", terms["L"]["variation_term"])
        self.assertIn("delta phi", terms["phi"]["variation_term"])
        self.assertIn("delta_matter X_TF", terms["matter"]["variation_term"])
        self.assertIn("H, L, phi, and matter", payload["variation_rule"])

    def test_fixed_xtf_residual_screen_and_scalar_trace_are_rejected(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rejected_routes"]}

        self.assertFalse(payload["xtf_fixed_by_hand_allowed"])
        self.assertFalse(payload["residual_source_allowed"])
        self.assertFalse(payload["two_d_screen_as_4d_source_allowed"])
        self.assertFalse(payload["scalar_trace_allowed"])
        self.assertEqual(
            set(rows),
            {
                "fixed_X_TF_by_hand",
                "residual_source",
                "two_d_screen_as_4d_source",
                "scalar_trace",
            },
        )
        self.assertTrue(all(not row["allowed"] for row in rows.values()))
        self.assertIn("cannot be held fixed", rows["fixed_X_TF_by_hand"]["reason"])
        self.assertIn("residual cancellation", rows["residual_source"]["reason"])
        self.assertIn("2D screen", rows["two_d_screen_as_4d_source"]["reason"])
        self.assertIn("trace-free rank-2", rows["scalar_trace"]["reason"])

    def test_markdown_reports_obligations_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Same-Bridge Dependency Gate", markdown)
        self.assertIn("Linear coupling: `int Q_TF^{ab} X_TF_ab`", markdown)
        self.assertIn("Obligations closed: 0/7", markdown)
        self.assertIn("X_TF fixed by hand allowed: False", markdown)
        self.assertIn("2D screen as 4D source allowed: False", markdown)
        self.assertIn("Scalar trace allowed: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
