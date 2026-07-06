from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_scross_transport_source_acceptance_gate import (
    build_payload,
    render_markdown,
)


class SCrossTransportSourceAcceptanceGateTests(unittest.TestCase):
    def test_math_shape_passes_but_source_acceptance_fails(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["route_status"], "math_shape_closed_source_not_accepted"
        )
        self.assertTrue(payload["ledger_ready"])
        self.assertFalse(payload["source_acceptance_ready"])
        self.assertFalse(payload["gate_passed"])
        self.assertTrue(payload["closure"]["weak_selector_math_shape_closed"])
        self.assertFalse(payload["closure"]["source_accepted_as_published_Janus"])

    def test_primary_blockers_are_source_functional_and_phi_l_law(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["primary_blocker"], "independent_S_cross_functional_found"
        )
        self.assertIn("phi_L_variation_law_found", payload["blockers"])
        self.assertIn("S_cross_transport_source_accepted", payload["blockers"])

    def test_no_fit_no_q_absorption_and_axiom_not_adopted(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["no_Qdet_Qcross_absorption"])
        self.assertTrue(closure["no_observational_fit"])
        self.assertTrue(closure["explicit_new_axiom_allowed"])
        self.assertTrue(closure["explicit_new_axiom_not_adopted"])

    def test_markdown_reports_negative_source_result(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("S_cross Transport Source Acceptance", markdown)
        self.assertIn("Gate passed: `False`", markdown)
        self.assertIn("new-axiom candidate", markdown)


if __name__ == "__main__":
    unittest.main()
