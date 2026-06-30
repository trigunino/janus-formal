from __future__ import annotations

import unittest

from scripts.build_p0_tracefree_h_source_candidate_matrix import (
    build_payload,
    render_markdown,
)


class P0TracefreeHSourceCandidateMatrixTests(unittest.TestCase):
    def test_matrix_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "tracefree-h-source-candidate-matrix-open")
        self.assertEqual(payload["candidate_count"], 6)
        self.assertEqual(payload["rejected_count"], 5)
        self.assertFalse(payload["any_candidate_accepted"])
        self.assertFalse(payload["source_selection_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["subgates_prediction_ready"])
        self.assertFalse(payload["source_requirement_gates"]["irrep_source_requirement_closed"])
        self.assertFalse(payload["source_requirement_gates"]["action_operator_requirement_closed"])
        self.assertFalse(payload["source_requirement_gates"]["projector_variation_dependency_closed"])
        self.assertFalse(payload["prediction"])
        self.assertFalse(payload["prediction_ready"])

    def test_all_requested_qtf_candidates_are_present_but_unaccepted(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["candidates"]}

        self.assertIn("janus_coupled_stress_stf", rows)
        self.assertIn("anisotropic_stress_pi_tf", rows)
        self.assertIn("weyl_shear", rows)
        self.assertIn("kinetic_quadrupole_vlasov", rows)
        self.assertIn("relative_metric_strain_action", rows)
        self.assertIn("bf_gl_phi_sigma", rows)
        self.assertTrue(all(row["selects_q_tf"] == "conditional" for row in rows.values()))
        self.assertFalse(any(row["janus_source_or_action"] for row in rows.values()))
        self.assertFalse(any(row["accepted"] for row in rows.values()))
        self.assertEqual(
            rows["janus_coupled_stress_stf"]["subgate"],
            "p0_tracefree_h_xtf_source_provenance_variation_contract",
        )
        self.assertEqual(rows["anisotropic_stress_pi_tf"]["subgate"], "p0_tracefree_h_anisotropic_stress_gate")
        self.assertEqual(rows["weyl_shear"]["subgate"], "p0_tracefree_h_weyl_shear_source_gate")
        self.assertEqual(rows["kinetic_quadrupole_vlasov"]["subgate"], "p0_tracefree_h_vlasov_quadrupole_gate")
        self.assertEqual(rows["relative_metric_strain_action"]["subgate"], "p0_tracefree_h_relative_strain_action_gate")
        self.assertEqual(rows["bf_gl_phi_sigma"]["subgate"], "p0_tracefree_h_bf_gl_phi_sigma_gate")
        self.assertFalse(any(row.get("subgate_prediction_ready", True) for row in rows.values() if "subgate" in row))

    def test_rejected_scalar_trace_fit_routes_are_named(self) -> None:
        rows = {row["candidate"]: row for row in build_payload()["rejected_routes"]}

        self.assertIn("density_scalar", rows)
        self.assertIn("pressure_scalar", rows)
        self.assertIn("b4vol_determinant", rows)
        self.assertIn("isotropic_flrw", rows)
        self.assertIn("residual_fit", rows)
        self.assertIn("rank-9 trace-free", rows["density_scalar"]["reason"])
        self.assertIn("volume trace", rows["b4vol_determinant"]["reason"])
        self.assertIn("not a Janus source/action", rows["residual_fit"]["reason"])
        self.assertFalse(any(row["accepted"] for row in rows.values()))

    def test_acceptance_rule_requires_janus_source_action(self) -> None:
        payload = build_payload()
        guardrails = " ".join(payload["guardrails"])

        self.assertEqual(payload["accepted_candidates"], [])
        self.assertIn("Janus source/action", payload["acceptance_rule"])
        self.assertIn("Janus source/action", guardrails)
        self.assertIn("residual fitting", guardrails)

    def test_markdown_reports_matrix_and_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Trace-Free H Source Candidate Matrix", markdown)
        self.assertIn("janus_coupled_stress_stf", markdown)
        self.assertIn("p0_tracefree_h_xtf_source_provenance_variation_contract", markdown)
        self.assertIn("anisotropic_stress_pi_tf", markdown)
        self.assertIn("bf_gl_phi_sigma", markdown)
        self.assertIn("p0_tracefree_h_anisotropic_stress_gate", markdown)
        self.assertIn("p0_tracefree_h_irrep_source_requirements_gate", markdown)
        self.assertIn("p0_tracefree_h_action_operator_requirements_gate", markdown)
        self.assertIn("p0_tracefree_h_projector_variation_dependency_gate", markdown)
        self.assertIn("p0_tracefree_h_janus_coupled_stress_stf_transport_gate", markdown)
        self.assertIn("p0_tracefree_h_weyl_shear_source_gate", markdown)
        self.assertIn("p0_tracefree_h_vlasov_quadrupole_gate", markdown)
        self.assertIn("p0_tracefree_h_relative_strain_action_gate", markdown)
        self.assertIn("p0_tracefree_h_bf_gl_phi_sigma_gate", markdown)
        self.assertIn("b4vol_determinant", markdown)
        self.assertIn("Any candidate accepted: False", markdown)
        self.assertIn("Prediction: False", markdown)


if __name__ == "__main__":
    unittest.main()
