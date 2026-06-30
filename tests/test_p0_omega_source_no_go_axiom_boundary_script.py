from __future__ import annotations

import unittest

from scripts.build_p0_omega_source_no_go_axiom_boundary import build_payload, render_markdown


class P0OmegaSourceNoGoAxiomBoundaryTests(unittest.TestCase):
    def test_failed_source_search_blocks_physics_promotion(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "source-no-go-or-explicit-axiom-boundary")
        self.assertFalse(payload["janus_source_audits_find_law"])
        self.assertEqual(payload["source_audit_result"], "no D_u L/Omega law found")
        self.assertFalse(payload["omega_u_zero_source_derived"])
        self.assertFalse(payload["without_source_law_promotes_to_physics"])
        self.assertEqual(payload["omega_u_zero_without_source_status"], "gauge/candidate")

    def test_axiom_route_is_explicit_rank_one_dust_only_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["explicit_axiom_available"])
        self.assertFalse(payload["explicit_axiom_adopted_here"])
        self.assertTrue(payload["if_adopted_is_new_axiom"])
        self.assertEqual(payload["if_adopted_scope"], "rank-one dust only")
        self.assertTrue(payload["rank_one_dust_scope_only"])
        self.assertFalse(payload["pressure_pi_closed"])
        self.assertFalse(payload["predictions_ready"])
        self.assertFalse(payload["fitted_closure"])
        self.assertIn("no new prediction", payload["scope"])

    def test_boundary_rows_cover_no_go_axiom_and_open_extensions(self) -> None:
        rows = " ".join(
            row["case"] + " " + row["premise"] + " " + row["boundary"] + " " + row["allowed_claim"]
            for row in build_payload()["boundary_rows"]
        )

        self.assertIn("no_source_law", rows)
        self.assertIn("current Janus source audits find no D_u L/Omega law", rows)
        self.assertIn("no promotion to physics", rows)
        self.assertIn("explicit_axiom_acceptance", rows)
        self.assertIn("new explicit no-fit axiom", rows)
        self.assertIn("rank-one dust scope only", rows)
        self.assertIn("pressure/Pi still open", rows)
        self.assertIn("no predictions", rows)

    def test_markdown_states_conditional_boundary(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("| case | premise | boundary | allowed claim |", markdown)
        self.assertIn("Without source law promotes to physics: False", markdown)
        self.assertIn("If adopted is new axiom: True", markdown)
        self.assertIn("Pressure/Pi closed: False", markdown)
        self.assertIn("cannot be promoted from gauge/candidate to physics", markdown)


if __name__ == "__main__":
    unittest.main()
