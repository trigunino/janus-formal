from __future__ import annotations

import unittest

from scripts.build_p0_source_derived_route_attempt import build_payload, render_markdown


class P0SourceDerivedRouteAttemptTests(unittest.TestCase):
    def test_attempt_checks_sources_but_finds_no_closure(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "attempt-open-no-source-closure-found")
        self.assertEqual(payload["sources_checked"], ["M15", "M30", "M31"])
        self.assertFalse(payload["source_derived_solution_found"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_each_source_has_usable_condition(self) -> None:
        attempts = {row["source"]: row for row in build_payload()["source_attempts"]}

        self.assertIn("S_int", attempts["M15"]["usable_condition"])
        self.assertIn("zero-divergence", attempts["M30"]["usable_condition"])
        self.assertIn("admissibility filter", attempts["M31"]["usable_condition"])
        self.assertTrue(all(not row["closed"] for row in attempts.values()))

    def test_candidate_solution_shape_forces_same_object(self) -> None:
        shape = " ".join(build_payload()["candidate_solution_shape"])

        self.assertIn("Omega_alpha=(D_alpha L)L^{-1}", shape)
        self.assertIn("same L and same path rule", shape)
        self.assertIn("R_plus=0 and R_minus=0", shape)

    def test_markdown_names_strongest_result(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Strongest result:", markdown)
        self.assertIn("M30 gives the sharpest target", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
