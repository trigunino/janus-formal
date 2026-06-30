from __future__ import annotations

import unittest

from scripts.build_p0_route_c_indirect_path_rule_source_audit import build_payload, render_markdown


class P0RouteCIndirectPathRuleSourceAuditTests(unittest.TestCase):
    def test_audit_finds_no_indirect_selector(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "indirect-path-rule-source-audit-open")
        self.assertEqual(payload["audited_source_count"], 7)
        self.assertEqual(payload["accepted_indirect_source_count"], 0)
        self.assertFalse(payload["indirect_path_rule_source_found"])
        self.assertTrue(payload["all_sources_filter_not_select"])
        self.assertTrue(payload["noether_action_possible_but_not_supplied"])
        self.assertTrue(payload["flrw_background_not_general_path_rule"])
        self.assertFalse(payload["prediction_ready"])

    def test_rows_cover_indirect_sources(self) -> None:
        sources = {row["source"] for row in build_payload()["rows"]}

        self.assertEqual(
            sources,
            {
                "bianchi_divergence",
                "noether_identity",
                "coupled_geodesics",
                "mirror_symmetry",
                "pt_geometry",
                "flrw_perturbed_limit",
                "kinetic_sheet_vlasov",
            },
        )

    def test_markdown_reports_filter_not_select(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Indirect Path-Rule Source Audit", markdown)
        self.assertIn("All sources filter not select: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
