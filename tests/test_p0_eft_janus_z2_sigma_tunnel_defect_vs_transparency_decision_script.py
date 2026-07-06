from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_tunnel_defect_vs_transparency_decision import (
    build_payload,
    render_markdown,
)


class TunnelDefectVsTransparencyDecisionTests(unittest.TestCase):
    def test_transparency_is_preferred_without_derived_defect(self) -> None:
        payload = build_payload()

        self.assertEqual(
            payload["decision_route"],
            "strict_transparency_preferred_until_defect_action_derived",
        )
        self.assertTrue(payload["decision_criteria"]["strict_Z2_bulk_force_cancels"])
        self.assertFalse(payload["decision_criteria"]["independent_tunnel_defect_action_source_found"])
        self.assertTrue(payload["gate_passed"])

    def test_total_counterterm_is_not_set_to_zero(self) -> None:
        consequences = build_payload()["consequences"]

        self.assertEqual(consequences["M30_bulk_channel_E_counterterm"], "0")
        self.assertFalse(consequences["may_set_total_E_counterterm_zero"])
        self.assertTrue(consequences["active_RSigma_certificate_still_blocked"])

    def test_next_route_is_embedding_and_junction_not_defect_guess(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["primary_blocker"], "active_metric_embedding_available")
        self.assertIn("do not invent a defect density", payload["next_required"])
        self.assertIn("junction stress", " ".join(payload["next_required"]))

    def test_markdown_records_decision(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Tunnel Defect vs Transparency", markdown)
        self.assertIn("strict Z2 transparency", markdown)


if __name__ == "__main__":
    unittest.main()
