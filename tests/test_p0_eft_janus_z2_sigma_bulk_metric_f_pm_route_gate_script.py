from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_bulk_metric_f_pm_route_gate import (
    build_payload,
    render_markdown,
)


class BulkMetricFpmRouteGateTests(unittest.TestCase):
    def test_forbids_unproven_f_pm_shortcuts(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["static_f_pm_values_ready"])
        self.assertTrue(payload["active_embedding_second_form_route_preferred"])
        self.assertEqual(
            payload["bibliography_route"]["DeltaK_route"],
            "active_embedding_second_form_first",
        )
        self.assertEqual(
            payload["primary_blocker"],
            "R_Sigma_solution_certificate_and_active_embedding_manifest",
        )
        self.assertIn(
            "Schwarzschild f_pm without Janus/Z2 static areal chart",
            payload["forbidden_substitutions"],
        )

    def test_routes_are_separated(self) -> None:
        routes = build_payload()["routes"]

        self.assertFalse(routes["static_areal_f_pm_route"]["ready"])
        self.assertTrue(routes["static_areal_f_pm_route"]["diagnostic_only_until_chart_derived"])
        self.assertTrue(routes["active_embedding_second_form_route"]["active_default_route"])

    def test_markdown_reports_decision(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Bulk Metric f_pm Route", markdown)
        self.assertIn("Embedding route preferred: `True`", markdown)


if __name__ == "__main__":
    unittest.main()
