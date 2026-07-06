from __future__ import annotations

import unittest

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_and_residual_counterterm_bibliography_gate import (
    build_payload,
    render_markdown,
)


class ActiveEmbeddingAndResidualCountertermBibliographyGateTests(unittest.TestCase):
    def test_selects_embedding_route_and_forbids_shortcuts(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["gate_passed"])
        self.assertTrue(payload["active_embedding_route_selected"])
        self.assertFalse(payload["non_GHY_counterterm_closes_for_free"])
        self.assertTrue(payload["artificial_counterterm_forbidden"])
        self.assertFalse(payload["route_decision"]["f_pm_shortcut_allowed"])

    def test_tracks_blockers(self) -> None:
        payload = build_payload()

        self.assertIn("R_Sigma_solution_certificate", payload["primary_blockers"])
        self.assertIn("metric_non_GHY_trace_R_h", payload["primary_blockers"])
        self.assertIn("extrinsic_non_GHY_trace_R_K", payload["primary_blockers"])

    def test_markdown_mentions_sources(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Mars-Senovilla-2002", markdown)
        self.assertIn("Capovilla-Guven-1995", markdown)
        self.assertIn("Corichi-WilsonEwing-2010", markdown)
        self.assertIn("Non-GHY closes for free: `False`", markdown)

    def test_holst_boundary_refs_do_not_close_counterterm(self) -> None:
        payload = build_payload()

        self.assertIn("Holst_boundary_variation_status", payload["route_decision"])
        self.assertFalse(payload["non_GHY_counterterm_closes_for_free"])
        self.assertIn(
            "extract_or_eliminate_R_h_trace_and_R_K_trace_from_that_projection",
            payload["next_required"],
        )


if __name__ == "__main__":
    unittest.main()
