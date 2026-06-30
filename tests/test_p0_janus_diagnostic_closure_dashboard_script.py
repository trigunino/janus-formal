from __future__ import annotations

import unittest

from scripts.build_p0_blocker_dependency_graph import build_payload as build_graph_payload
from scripts.build_p0_janus_diagnostic_closure_dashboard import build_payload, render_markdown


class P0JanusDiagnosticClosureDashboardScriptTests(unittest.TestCase):
    def test_dashboard_aggregates_non_predictive_probes(self) -> None:
        payload = build_payload()
        graph = build_graph_payload()
        probes = {row["probe"] for row in payload["probe_rows"]}

        self.assertTrue(payload["blocker_graph_consumed"])
        self.assertEqual(payload["graph_open_blockers"], graph["open_blockers"])
        self.assertEqual(payload["graph_all_blockers_closed"], graph["all_blockers_closed"])
        self.assertEqual(payload["source_residual_matrix_status"], graph["source_residual_matrix_status"])
        self.assertIn("p0_janus_lgeom_dl_lie_residual_probe", probes)
        self.assertIn("p0_janus_weakfield_b4vol_product_rule_probe", probes)
        self.assertIn("p0_janus_two_sector_metric_force_vlasov_probe", probes)
        self.assertTrue(payload["all_probe_reports_non_predictive"])
        self.assertTrue(payload["all_probe_reports_diagnostic"])
        self.assertEqual(payload["physics_closed"], graph["physics_closed"])
        self.assertEqual(payload["prediction_ready"], graph["prediction_ready"])

    def test_dashboard_forbids_scalar_absorption_and_promotions(self) -> None:
        payload = build_payload()
        graph = build_graph_payload()
        graph_rows = {row["blocker"]: row for row in graph["blockers"]}
        text = " ".join(payload["blocking_findings"] + [payload["verdict"]])

        self.assertIn("raw L_geom", text)
        self.assertIn("D L", text)
        self.assertIn("B4vol", text)
        self.assertIn("R_plus/R_minus", text)
        self.assertIn("Q_det/Q_cross absorption", text)
        self.assertFalse(payload["raw_lgeom_promoted"])
        self.assertEqual(payload["dl_source_derived"], graph_rows["D L transport law"]["closed"])
        self.assertEqual(payload["b4vol_source_law_derived"], graph_rows["D log B_4vol measure law"]["closed"])
        self.assertEqual(
            payload["source_selected_metric_branch"],
            graph_rows["source-measure branch selection"]["closed"],
        )
        self.assertEqual(payload["same_l_transport_closed"], graph_rows["D L transport law"]["closed"])
        self.assertEqual(
            payload["source_residual_closure_obligation_matrix_available"],
            graph["janus_source_residual_closure_obligation_matrix_available"],
        )
        self.assertTrue(all(row["open_blockers"] for row in payload["probe_rows"]))

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("p0_janus_lgeom_tetrad_map_residual_probe", markdown)
        self.assertIn("Per-Probe Open Blockers", markdown)
        self.assertIn("without Q_det/Q_cross absorption", markdown)


if __name__ == "__main__":
    unittest.main()
