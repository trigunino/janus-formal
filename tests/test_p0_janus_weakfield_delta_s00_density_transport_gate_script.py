from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_delta_s00_density_transport_gate import (
    build_payload,
    render_markdown,
)


class P0JanusWeakfieldDeltaS00DensityTransportGateTests(unittest.TestCase):
    def test_density_transport_slot_is_written_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "delta-s00-density-transport-slot-written-physics-open")
        self.assertTrue(payload["field_residual_convention_selected"])
        self.assertEqual(payload["selected_field_residual_convention"], "proper_density_input")
        self.assertTrue(payload["single_cross_dust_effective_continuity_closed"])
        self.assertTrue(payload["density_response_chain_rule_closed"])
        self.assertTrue(payload["receiver_measure_response_closed"])
        self.assertFalse(payload["source_pullback_metric_response_closed"])
        self.assertEqual(
            payload["phi_l_map_response_artifact"],
            "p0_janus_weakfield_phi_l_map_density_response_gate",
        )
        self.assertTrue(payload["delta_phi_map_response_slot_closed"])
        self.assertFalse(payload["dynamic_phi_l_selection_closed"])
        self.assertFalse(payload["mirror_map_response_closed"])
        self.assertTrue(payload["weakfield_density_transport_slot_written"])
        self.assertFalse(payload["full_density_transport_closed"])
        self.assertFalse(payload["pressure_pi_transport_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_transport_rows_keep_proper_and_effective_slots_separate(self) -> None:
        rows = {row["name"]: row for row in build_payload()["transport_rows"]}

        self.assertIn("delta_rho_other_to_self", rows["proper_density_transport_slot"]["formula"])
        self.assertIn("delta_phi_map_response", rows["proper_density_transport_slot"]["formula"])
        self.assertIn("B_4vol rho_other_to_self", rows["effective_current_continuity"]["formula"])
        self.assertIn("rho0_other_to_self delta_B_4vol", rows["effective_density_response"]["formula"])
        self.assertIn("proper_density_input", rows["delta_s00_input_rule"]["formula"])
        self.assertIn("do not feed rho_eff and B_4vol together", rows["delta_s00_input_rule"]["formula"])

    def test_open_requirements_keep_phi_l_mirror_and_pressure_open(self) -> None:
        requirements = " ".join(build_payload()["open_requirements"])

        self.assertIn("same Janus phi/L branch", requirements)
        self.assertIn("mirror plus/minus", requirements)
        self.assertIn("source pullback metric response", requirements)
        self.assertIn("pressure/Pi", requirements)

    def test_no_fit_or_scalar_absorption(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_full_transport(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Delta S00 Density Transport", markdown)
        self.assertIn("Delta phi map response slot closed: True", markdown)
        self.assertIn("Dynamic phi/L selection closed: False", markdown)
        self.assertIn("Weakfield density transport slot written: True", markdown)
        self.assertIn("Full density transport closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
