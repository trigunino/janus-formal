from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_scross_phi_l_variation_law_gate import (
    build_payload,
    render_markdown,
)


class SCrossPhiLVariationLawGateTests(unittest.TestCase):
    def test_template_is_ready_but_law_is_not_closed(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["conditional_template_ready"])
        self.assertFalse(payload["phi_l_variation_law_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertEqual(
            payload["route_status"],
            "conditional_template_ready_waiting_for_independent_scross",
        )

    def test_independent_scross_is_primary_blocker(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["primary_blocker"], "independent_S_cross_functional_found"
        )
        self.assertIn("plus_phi_L_variation_law_derived", payload["blockers"])
        self.assertFalse(payload["feeds"]["plus_transport_compatibility_source_derived"])

    def test_same_bridge_no_fit_template_is_preserved(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["same_bridge_for_stress_and_Qcross"])
        self.assertTrue(closure["determinant_factors_kept_outside_bridge"])
        self.assertTrue(closure["no_multiplier_route"])

    def test_markdown_reports_conditional_target(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Phi/L Variation Law", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("conditional theorem target", markdown)


if __name__ == "__main__":
    unittest.main()
