from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_force_source_route_decision_gate import (
    build_payload,
    render_markdown,
)


class ForceSourceRouteDecisionGateTests(unittest.TestCase):
    def test_embedding_route_is_preferred_without_closing_routes(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertEqual(payload["preferred_next_attack"], "embedding_route")
        self.assertEqual(payload["main_branch_next_blocker"], "R_Sigma_solution_certificate")
        self.assertEqual(payload["auxiliary_route"], "phi_L_route")
        self.assertFalse(payload["upstream"]["source_force"]["ready"])

    def test_route_scores_keep_phi_l_auxiliary(self) -> None:
        routes = build_payload()["routes"]

        self.assertLess(routes["embedding_route"]["score"], routes["phi_L_route"]["score"])
        self.assertEqual(routes["embedding_route"]["status"], "preferred_next_attack")
        self.assertEqual(routes["phi_L_route"]["status"], "auxiliary_open")
        self.assertIn("independent_S_cross_functional_found", routes["phi_L_route"]["hard_blockers"])

    def test_closure_refuses_premature_route_closure(self) -> None:
        closure = build_payload()["closure"]

        self.assertTrue(closure["no_route_closed_prematurely"])
        self.assertTrue(closure["no_auxiliary_route_archived"])
        self.assertTrue(closure["embedding_route_preferred_for_next_attack"])

    def test_markdown_reports_main_blocker(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Force Source Route Decision", markdown)
        self.assertIn("R_Sigma_solution_certificate", markdown)
        self.assertIn("phi/L route stays auxiliary", markdown)


if __name__ == "__main__":
    unittest.main()
