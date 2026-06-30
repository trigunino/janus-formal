from __future__ import annotations

import unittest

from scripts.build_p0_phi_j_l_remaining_lock_decision_matrix import (
    build_payload,
    render_markdown,
)


class P0PhiJLRemainingLockDecisionMatrixTests(unittest.TestCase):
    def test_general_m15_m30_route_is_bounded_no_go(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rows"]}

        self.assertEqual(payload["status"], "phi-j-l-remaining-lock-open")
        self.assertTrue(payload["underselection_proved_for_family"])
        self.assertTrue(payload["b4vol_jacobian_gauge_degeneracy_proved"])
        self.assertFalse(payload["source_b4vol_alone_selects_jphi"])
        self.assertTrue(payload["requires_slice_lapse_selector"])
        self.assertTrue(payload["janus_equations_select_b4vol_weight"])
        self.assertFalse(payload["janus_equations_select_phi_without_extra_gauge"])
        self.assertFalse(payload["general_perturbed_branch_lapse_slice_fixed"])
        self.assertTrue(payload["m15_m30_only_bounded_no_go_for_general_selector"])
        self.assertFalse(rows["m15_m30_only_general_perturbed"]["selects_unique_phi_j_l"])

    def test_conditional_and_new_principle_routes_are_labeled(self) -> None:
        payload = build_payload()
        rows = {row["route"]: row for row in payload["rows"]}

        self.assertTrue(payload["clean_conditional_flrw_route_available"])
        self.assertTrue(rows["flrw_comoving_conditional"]["selects_unique_phi_j_l"])
        self.assertEqual(rows["flrw_comoving_conditional"]["status"], "conditional")
        self.assertFalse(rows["flrw_comoving_conditional"]["source_derived"])
        self.assertEqual(rows["intrinsic_minimal_distortion"]["status"], "new-principle")
        self.assertFalse(rows["intrinsic_minimal_distortion"]["source_derived"])
        self.assertEqual(rows["strong_boundary_or_gauge_selector"]["status"], "new-boundary-axiom")
        self.assertFalse(rows["strong_boundary_or_gauge_selector"]["source_derived"])

    def test_no_shortcut_to_prediction_claim(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["clean_general_route_without_new_axiom_found"])
        self.assertTrue(payload["new_axiom_required_for_general_perturbed_selection"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_qdet_qcross_absorption"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_exposes_remaining_lock(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("M15/M30-only bounded no-go for general selector: True", markdown)
        self.assertIn("B4vol/Jacobian gauge degeneracy proved: True", markdown)
        self.assertIn("Source B4vol alone selects J_phi: False", markdown)
        self.assertIn("Clean general route without new axiom found: False", markdown)
        self.assertIn("New axiom required for general perturbed selection: True", markdown)
        self.assertIn("m15_m30_only_general_perturbed", markdown)
        self.assertIn("intrinsic_minimal_distortion", markdown)
        self.assertIn("full_phi_or_scouple_action", markdown)


if __name__ == "__main__":
    unittest.main()
