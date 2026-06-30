from __future__ import annotations

import unittest

from scripts.build_p0_janus_kinetic_closure_routes_decision import build_payload, render_markdown


class P0JanusKineticClosureRoutesDecisionTests(unittest.TestCase):
    def test_routes_include_cold_isotropic_truncated_and_vlasov(self) -> None:
        routes = {row["route"]: row for row in build_payload()["routes"]}

        self.assertIn("cold_dust", routes)
        self.assertIn("isotropic_dispersion", routes)
        self.assertIn("truncated_moment", routes)
        self.assertIn("full_vlasov", routes)
        self.assertEqual(routes["truncated_moment"]["allowed"], "rejected_without_source")

    def test_only_cold_dust_is_currently_conditional(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["cold_dust_allowed_conditionally"])
        self.assertFalse(payload["isotropic_dispersion_closed"])
        self.assertFalse(payload["truncated_moment_allowed_without_source"])
        self.assertFalse(payload["full_vlasov_route_selected"])
        self.assertTrue(payload["full_vlasov_moment_closure_contract_available"])
        self.assertTrue(payload["pi_zero_preservation_gate_available"])
        self.assertTrue(payload["vlasov_geodesic_force_target_available"])
        self.assertTrue(payload["eos_prho_no_go_vlasov_gate_available"])

    def test_next_work_forbids_unsourced_truncation(self) -> None:
        work = " ".join(build_payload()["next_work"])

        self.assertIn("do not set Q_ijk=0", work)
        self.assertIn("p0_janus_full_vlasov_moment_closure_contract", work)
        self.assertIn("p0_janus_pi_zero_preservation_gate", work)
        self.assertIn("p0_janus_vlasov_geodesic_force_target", work)
        self.assertIn("p0_janus_eos_prho_no_go_vlasov_gate", work)
        self.assertIn("source-preserved isotropic", build_payload()["verdict"])

    def test_no_fit_or_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Truncated moment allowed without source: False", markdown)


if __name__ == "__main__":
    unittest.main()
