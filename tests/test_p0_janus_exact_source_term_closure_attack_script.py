from __future__ import annotations

import unittest

from scripts.build_p0_janus_exact_source_term_closure_attack import (
    build_payload,
    render_markdown,
)


class P0JanusExactSourceTermClosureAttackTests(unittest.TestCase):
    def test_best_route_is_soldered_same_l_without_fit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "best-route-selected-tetrad-soldered-same-l-open")
        self.assertTrue(payload["measure_candidate_fixed"])
        self.assertFalse(payload["boundary_gauge_candidate_fixed"])
        self.assertTrue(payload["l_candidate_route_selected"])
        self.assertEqual(payload["l_candidate_route"], "tetrad_soldered_same_l")
        self.assertEqual(
            payload["soldered_l_substitution_artifact"],
            "p0_janus_soldered_l_substitution_residual_gate",
        )
        self.assertTrue(payload["soldered_l_derivation_available"])
        self.assertEqual(
            payload["metric_pullback_compatibility_artifact"],
            "p0_janus_metric_pullback_compatibility_gate",
        )
        self.assertTrue(payload["metric_pullback_compatibility_derived"])
        self.assertFalse(payload["requires_observational_fit"])
        self.assertFalse(payload["introduces_new_axiom"])
        self.assertFalse(payload["prediction_ready"])

    def test_closure_axes_cover_measure_boundary_l_ephi_el(self) -> None:
        axes = {row["axis"]: row for row in build_payload()["closure_axes"]}

        self.assertIn("B_4vol", axes["measure"]["candidate_formula"])
        self.assertIn("xi|boundary=0", axes["boundary_gauge"]["candidate_formula"])
        self.assertIn("e_self^{-1} dphi e_to", axes["l_sector"]["candidate_formula"])
        self.assertIn("Lie_xi", axes["e_phi"]["candidate_formula"])
        self.assertIn("antisym_AB", axes["e_l"]["candidate_formula"])

    def test_route_tests_reject_insufficient_routes(self) -> None:
        rows = {row["route"]: row for row in build_payload()["route_tests"]}

        self.assertTrue(rows["pure_pullback_volume"]["fixes_measure"])
        self.assertFalse(rows["pure_pullback_volume"]["fixes_l"])
        self.assertFalse(rows["independent_l_lorentz_variation"]["fixes_l"])
        self.assertTrue(rows["tetrad_soldered_same_l"]["fixes_l"])
        self.assertIn("best no-rustine", rows["tetrad_soldered_same_l"]["verdict"])

    def test_markdown_states_next_derivations(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Exact Source Term Closure Attack", markdown)
        self.assertIn("L candidate route: `tetrad_soldered_same_l`", markdown)
        self.assertIn("p0_janus_soldered_l_substitution_residual_gate", markdown)
        self.assertIn("p0_janus_metric_pullback_compatibility_gate", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
