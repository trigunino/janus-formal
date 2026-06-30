from __future__ import annotations

import unittest

from scripts.build_p0_janus_weakfield_delta_phi_psi_source_chain_gate import (
    build_payload,
    render_markdown,
)


class P0JanusWeakfieldDeltaPhiPsiSourceChainGateTests(unittest.TestCase):
    def test_chain_is_written_but_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "delta-phi-psi-source-chain-written-physics-open")
        self.assertTrue(payload["source_potential_rows_written"])
        self.assertTrue(payload["slip_rows_written"])
        self.assertTrue(payload["b4vol_feedback_written"])
        self.assertEqual(
            payload["delta_s00_expansion_artifact"],
            "p0_janus_weakfield_delta_s00_source_expansion_gate",
        )
        self.assertTrue(payload["delta_s00_expansion_closed"])
        self.assertFalse(payload["delta_s00_physics_closed"])
        self.assertEqual(
            payload["delta_s00_measure_convention_artifact"],
            "p0_janus_weakfield_delta_s00_measure_convention_gate",
        )
        self.assertTrue(payload["delta_s00_measure_convention_algebra_closed"])
        self.assertTrue(payload["delta_s00_field_residual_convention_selected"])
        self.assertEqual(payload["delta_s00_selected_field_residual_convention"], "proper_density_input")
        self.assertFalse(payload["delta_s00_source_convention_selected"])
        self.assertEqual(
            payload["delta_s00_density_transport_artifact"],
            "p0_janus_weakfield_delta_s00_density_transport_gate",
        )
        self.assertTrue(payload["delta_s00_density_transport_slot_written"])
        self.assertFalse(payload["delta_s00_full_density_transport_closed"])
        self.assertTrue(payload["delta_psi_poisson_row_derived"])
        self.assertTrue(payload["delta_phi_definition_closed"])
        self.assertFalse(payload["general_slip_source_closed"])
        self.assertFalse(payload["source_potential_solution_closed"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_chain_rows_link_delta_psi_and_delta_phi(self) -> None:
        rows = {row["name"]: row for row in build_payload()["chain_rows"]}

        self.assertIn("2 Lap(Delta_Psi)", rows["delta_psi_poisson"]["equation"])
        self.assertIn("delta_S00_minus-delta_S00_plus", rows["delta_psi_poisson"]["equation"])
        self.assertIn("Phi_plus-Psi_plus", rows["plus_slip"]["equation"])
        self.assertIn("Phi_minus-Psi_minus", rows["minus_slip"]["equation"])
        self.assertIn("Delta_Phi=Delta_Psi", rows["delta_phi_from_delta_psi_and_slip"]["equation"])
        self.assertTrue(rows["delta_psi_poisson"]["closed"])
        self.assertFalse(rows["plus_slip"]["closed"])
        self.assertFalse(rows["minus_slip"]["closed"])

    def test_dust_slip_is_conditional_not_general_closure(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["delta_phi_requires_slip"])
        self.assertTrue(payload["dust_delta_phi_equals_delta_psi_conditional"])
        self.assertFalse(payload["general_slip_source_closed"])
        self.assertFalse(payload["boundary_gauge_closed"])

    def test_no_qdet_absorption_or_fit(self) -> None:
        payload = build_payload()
        requirements = " ".join(payload["open_requirements"])

        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertIn("Q_det as density convention only", requirements)
        self.assertIn("boundary/gauge", requirements)

    def test_markdown_reports_open_status(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Delta Phi/Psi Source Chain", markdown)
        self.assertIn("Delta Psi Poisson row derived: True", markdown)
        self.assertIn("Delta S00 expansion closed: True", markdown)
        self.assertIn("Delta S00 physics closed: False", markdown)
        self.assertIn("Delta S00 measure convention algebra closed: True", markdown)
        self.assertIn("Delta S00 field residual convention selected: True", markdown)
        self.assertIn("Delta S00 selected field residual convention: `proper_density_input`", markdown)
        self.assertIn("Delta S00 source convention selected: False", markdown)
        self.assertIn("Delta S00 density transport slot written: True", markdown)
        self.assertIn("Delta S00 full density transport closed: False", markdown)
        self.assertIn("General slip source closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
