from __future__ import annotations

import unittest

from scripts.build_p0_shared_phi_j_source_selection_gate import build_payload, render_markdown


class P0SharedPhiJSourceSelectionGateTests(unittest.TestCase):
    def test_gate_is_open_with_local_identities_ready(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "shared-phi-j-source-selection-gate-open")
        self.assertTrue(payload["all_local_identities_ready"])
        self.assertTrue(payload["mirror_inverse_consistency_closed"])
        self.assertTrue(payload["integrability_route_source_compatible"])
        self.assertTrue(payload["underselection_probe_available"])
        self.assertTrue(payload["local_underselection_proved"])
        self.assertFalse(payload["unique_phi_j_l_selected"])
        self.assertTrue(payload["requires_new_axiom_or_source_action"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["phi_scouple_source_or_axiom_closed"])
        self.assertFalse(payload["all_consumers_source_selected"])
        self.assertFalse(payload["shared_source_selected_phi_j_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_consumers_cover_cuu_falpha_and_b4vol(self) -> None:
        consumers = {row["consumer"] for row in build_payload()["rows"]}

        self.assertEqual(consumers, {"Cuu", "F_alpha", "B_4vol"})

    def test_selection_obligations_isolate_remaining_physical_gap(self) -> None:
        obligations = {row["name"]: row for row in build_payload()["selection_obligations"]}

        self.assertTrue(obligations["mirror_inverse"]["closed"])
        self.assertTrue(obligations["integrability_route"]["closed"])
        self.assertFalse(obligations["dynamic_source_action"]["closed"])
        self.assertFalse(obligations["underselection_resolved"]["closed"])
        self.assertFalse(obligations["phi_scouple_source"]["closed"])

    def test_forbids_independent_maps_and_scalar_absorption(self) -> None:
        text = " ".join(build_payload()["forbidden_shortcuts"])

        self.assertIn("one phi/J for Cuu and another for B4vol", text)
        self.assertIn("one L/J for F_alpha", text)
        self.assertIn("Q_det", text)
        self.assertIn("Q_cross", text)

    def test_markdown_keeps_prediction_false(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("All local identities ready: True", markdown)
        self.assertIn("Local underselection proved: True", markdown)
        self.assertIn("Selection Obligations", markdown)
        self.assertIn("dynamic_source_action", markdown)
        self.assertIn("Shared source-selected phi/J closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
