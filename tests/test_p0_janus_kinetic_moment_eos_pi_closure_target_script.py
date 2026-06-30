from __future__ import annotations

import unittest

from scripts.build_p0_janus_kinetic_moment_eos_pi_closure_target import (
    build_payload,
    decompose_second_moment,
    render_markdown,
)


class P0JanusKineticMomentEosPiClosureTargetTests(unittest.TestCase):
    def test_second_moment_decomposition_is_trace_free(self) -> None:
        decomposition = decompose_second_moment()

        self.assertEqual(decomposition["trace_Pi"], 0)
        self.assertIn("P_xx", str(decomposition["p"]))

    def test_payload_defines_moments_and_routes(self) -> None:
        payload = build_payload()
        moments = {row["moment"] for row in payload["moment_definitions"]}
        routes = {row["route"]: row for row in payload["closure_routes"]}

        self.assertIn("density", moments)
        self.assertIn("momentum", moments)
        self.assertIn("stress", moments)
        self.assertIn("pressure", moments)
        self.assertIn("anisotropic_stress", moments)
        self.assertEqual(routes["cold_dust"]["closed"], "conditional")
        self.assertFalse(routes["full_kinetic"]["closed"])

    def test_kinetic_route_closes_algebra_not_hierarchy(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "kinetic-moment-eos-pi-closure-open")
        self.assertTrue(payload["second_moment_decomposition_derived"])
        self.assertTrue(payload["trace_free_pi_verified"])
        self.assertTrue(payload["dust_limit_recovers_p_zero_pi_zero"])
        self.assertFalse(payload["eos_from_kinetic_moments_closed"])
        self.assertFalse(payload["pi_evolution_from_kinetic_moments_closed"])
        self.assertFalse(payload["hierarchy_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_forbids_fit_by_omission(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_reports_hierarchy_open(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Hierarchy closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
