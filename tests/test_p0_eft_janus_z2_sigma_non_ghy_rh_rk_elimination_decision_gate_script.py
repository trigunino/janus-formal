from __future__ import annotations

import unittest

from scripts.derive_p0_eft_janus_z2_sigma_non_ghy_rh_rk_elimination_decision_gate import (
    build_payload,
    render_markdown,
)


class NonGhyRhRkEliminationDecisionGateTests(unittest.TestCase):
    def test_blocks_without_component_values_or_parity(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["gate_passed"])
        self.assertFalse(payload["R_h_R_K_eliminated"])
        self.assertFalse(payload["R_h_R_K_materializable"])
        self.assertEqual(
            payload["primary_blocker"],
            "alpha_res_component_values_or_componentwise_parity",
        )

    def test_forbids_zero_or_linear_k_shortcuts(self) -> None:
        payload = build_payload()

        self.assertIn(
            "do_not_emit_zero_R_h_R_K_while_non_GHY_channels_open",
            payload["forbidden_shortcuts"],
        )
        self.assertIn("do_not_reintroduce_linear_K_counterterm", payload["forbidden_shortcuts"])

    def test_markdown_reports_routes(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Non-GHY R_h/R_K", markdown)
        self.assertIn("Z2_anti_invariance_route", markdown)
        self.assertIn("explicit_alpha_value_route", markdown)


if __name__ == "__main__":
    unittest.main()
