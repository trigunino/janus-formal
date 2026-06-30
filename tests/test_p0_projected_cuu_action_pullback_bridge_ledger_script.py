from __future__ import annotations

import unittest

from scripts.build_p0_projected_cuu_action_pullback_bridge_ledger import (
    build_payload,
    render_markdown,
)


class P0ProjectedCuuActionPullbackBridgeLedgerTests(unittest.TestCase):
    def test_bridge_ledger_is_open_and_non_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "projected-cuu-action-pullback-bridge-ledger-open")
        self.assertTrue(payload["dust_monoflux_cuu_conditional_available"])
        self.assertFalse(payload["dust_monoflux_action_derivation_supplied"])
        self.assertTrue(payload["single_cross_dust_bridge_closed"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["projected_cuu_action_bridge_closed"])
        self.assertFalse(payload["r_plus_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_bridge_rows_cover_action_variation_dynamic_mirror_and_integrability(self) -> None:
        payload = build_payload()
        obligations = {row["obligation"] for row in payload["bridge_rows"]}
        anchors = {row["obligation"]: row["current_anchor"] for row in payload["bridge_rows"]}

        self.assertIn("pullback_dust_action", obligations)
        self.assertIn("projected_el_variation", obligations)
        self.assertIn("same_phi_l_map", obligations)
        self.assertIn("dynamic_phi_l_selection", obligations)
        self.assertIn("mirror_inverse", obligations)
        self.assertIn("integrability", obligations)
        self.assertEqual(anchors["mirror_inverse"], "p0_cuu_inverse_map_integrability_target")
        self.assertEqual(anchors["integrability"], "p0_cuu_inverse_map_integrability_target")
        self.assertTrue(payload["inverse_c_relation_written"])
        self.assertTrue(payload["jacobian_from_same_l_written"])

    def test_forbidden_operations_prevent_axiom_promotion(self) -> None:
        forbidden = " ".join(build_payload()["forbidden_operations"])

        self.assertIn("do not impose hE=rho hCuu", forbidden)
        self.assertIn("different phi/L", forbidden)
        self.assertIn("pressure/Pi", forbidden)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Prediction ready: False", markdown)
        self.assertIn("Dust monoflux Cuu conditional available: True", markdown)
        self.assertIn("dynamic_phi_l_selection", markdown)


if __name__ == "__main__":
    unittest.main()
