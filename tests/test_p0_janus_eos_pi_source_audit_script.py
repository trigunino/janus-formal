from __future__ import annotations

import unittest

from scripts.build_p0_janus_eos_pi_source_audit import build_payload, render_markdown


class P0JanusEosPiSourceAuditTests(unittest.TestCase):
    def test_sources_supply_signs_not_eos_or_pi_law(self) -> None:
        payload = build_payload()
        rows = " ".join(row["source"] + " " + row["does_not_supply"] for row in payload["source_rows"])

        self.assertTrue(payload["pressure_sign_source_verified"])
        self.assertIn("M15", rows)
        self.assertIn("equation of state", rows)
        self.assertIn("Pi evolution", rows)
        self.assertFalse(payload["equation_of_state_source_derived"])

    def test_closure_routes_keep_dust_conditional(self) -> None:
        routes = {row["route"]: row for row in build_payload()["closure_routes"]}

        self.assertEqual(routes["dust"]["status"], "conditional")
        self.assertEqual(routes["barotropic_perfect_fluid"]["status"], "open")
        self.assertEqual(routes["kinetic_moments"]["status"], "open")
        self.assertEqual(routes["pi_zero_proof"]["status"], "open")

    def test_secondary_kinetic_route_does_not_close_physics(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["kinetic_route_available_as_secondary_source"])
        self.assertFalse(payload["pi_evolution_source_derived"])
        self.assertFalse(payload["pi_zero_source_proved"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_fit(self) -> None:
        self.assertFalse(build_payload()["uses_observational_fit"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Equation of state source-derived: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
