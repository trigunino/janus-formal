from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_scross_m30_boundary_reduction_audit_gate import (
    build_payload,
    render_markdown,
)


class M30BoundaryReductionAuditGateTests(unittest.TestCase):
    def test_janus_sources_are_available_but_sigma_reduction_is_not(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["route_status"], "janus-action-found-sigma-reduction-not-found"
        )
        self.assertTrue(payload["closure"]["janus_two_layer_action_source_available"])
        self.assertTrue(payload["closure"]["janus_bivariation_source_available"])
        self.assertTrue(
            payload["closure"]["conditional_bulk_to_sigma_force_formula_derived"]
        )
        self.assertTrue(payload["closure"]["strict_Z2_bulk_force_cancels"])
        self.assertFalse(
            payload["closure"]["can_reduce_M30_interaction_terms_to_Sigma_counterterm"]
        )
        self.assertFalse(payload["gate_passed"])

    def test_blockers_are_specific_to_sigma_pullback_and_transport(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["primary_blocker"], "explicit_S_Sbar_to_Sigma_pullback_found"
        )
        self.assertIn("explicit_phi_L_transport_from_M30_found", payload["blockers"])
        self.assertIn("explicit_counterterm_density_from_M30_found", payload["blockers"])

    def test_conditional_bulk_to_sigma_reduction_is_recorded(self) -> None:
        payload = build_payload()["bulk_to_sigma_reduction"]

        self.assertTrue(payload["conditional_force_formula_derived"])
        self.assertFalse(payload["explicit_counterterm_density_derived"])
        self.assertEqual(payload["primary_blocker"], "active_embedding_X_pm")

    def test_strict_z2_cancellation_blocks_m30_bulk_counterterm(self) -> None:
        payload = build_payload()["strict_Z2_force_cancellation"]

        self.assertFalse(payload["bulk_M30_generates_counterterm"])
        self.assertEqual(payload["E_counterterm_from_bulk_M30"], "0")
        self.assertTrue(payload["need_tunnel_defect_for_nonzero_counterterm"])

    def test_bibliography_is_generic_not_janus_sigma_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["closure"]["generic_boundary_variation_bibliography_available"])
        self.assertTrue(payload["closure"]["generic_junction_bibliography_available"])
        self.assertFalse(
            any(row["provides_janus_sigma_reduction"] for row in payload["external_bibliography"])
        )

    def test_markdown_reports_no_closure(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("M30 Boundary Reduction", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("strict Z2 descent cancels", markdown)


if __name__ == "__main__":
    unittest.main()
