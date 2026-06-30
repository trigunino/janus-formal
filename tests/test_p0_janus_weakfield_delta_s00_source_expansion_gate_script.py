from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_delta_s00_source_expansion_gate import (
    build_payload,
    delta_b_minus_reduced,
    delta_b_plus_reduced,
    dust_slip_relative_source,
    render_markdown,
    source_expansions,
    symbols,
)


class P0JanusWeakfieldDeltaS00SourceExpansionGateTests(unittest.TestCase):
    def test_delta_b_reduction_matches_delta_phi_delta_psi(self) -> None:
        s = symbols()

        self.assertEqual(delta_b_plus_reduced(), s["Delta_Phi"] - 3 * s["Delta_Psi"])
        self.assertEqual(delta_b_minus_reduced(), -s["Delta_Phi"] + 3 * s["Delta_Psi"])
        self.assertEqual(sp.simplify(delta_b_plus_reduced() + delta_b_minus_reduced()), 0)

    def test_source_expansions_keep_b4vol_feedback_and_signs(self) -> None:
        s = symbols()
        rows = source_expansions()

        expected_plus = (
            s["delta_rho_plus"]
            + s["delta_rho_minus_to_plus"]
            + s["rho0_minus_to_plus"] * (s["Delta_Phi"] - 3 * s["Delta_Psi"])
        )
        expected_minus = -(
            s["delta_rho_minus"]
            + s["delta_rho_plus_to_minus"]
            + s["rho0_plus_to_minus"] * (-s["Delta_Phi"] + 3 * s["Delta_Psi"])
        )

        self.assertEqual(sp.simplify(rows["delta_S00_plus"] - expected_plus), 0)
        self.assertEqual(sp.simplify(rows["delta_S00_minus"] - expected_minus), 0)
        self.assertEqual(
            sp.simplify(rows["delta_S00_minus_minus_plus"] - (expected_minus - expected_plus)),
            0,
        )

    def test_dust_slip_reduction_substitutes_delta_phi_equals_delta_psi(self) -> None:
        s = symbols()
        expected = source_expansions()["delta_S00_minus_minus_plus"].subs(
            s["Delta_Phi"], s["Delta_Psi"]
        )

        self.assertEqual(sp.simplify(dust_slip_relative_source() - expected), 0)

    def test_payload_is_algebra_closed_but_physics_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "delta-s00-source-expansion-algebra-closed-physics-open")
        self.assertTrue(payload["delta_s00_expansion_closed"])
        self.assertTrue(payload["relative_source_written"])
        self.assertFalse(payload["density_transport_closed"])
        self.assertFalse(payload["background_subtraction_closed"])
        self.assertFalse(payload["qdet_convention_selected_from_source"])
        self.assertFalse(payload["slip_source_closed"])
        self.assertFalse(payload["boundary_gauge_closed"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["qdet_absorption_allowed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_no_absorption(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Delta S00 Source Expansion", markdown)
        self.assertIn("Delta S00 expansion closed: True", markdown)
        self.assertIn("Qdet absorption allowed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
