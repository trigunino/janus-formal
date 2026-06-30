from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_g0i_shift_operator_derivation import (
    build_payload,
    derive_g0i_operator,
    render_markdown,
)


class P0JanusWeakfieldG0iShiftOperatorDerivationTests(unittest.TestCase):
    def test_operator_matches_linearized_einstein_result(self) -> None:
        psi_ti, div_shift_i, lap_shift_i = sp.symbols("Psi_ti divB_i lapB_i")
        operator = derive_g0i_operator()

        self.assertEqual(operator["full"], 2 * psi_ti + (div_shift_i - lap_shift_i) / 2)
        self.assertEqual(operator["transverse_quasistatic"], -lap_shift_i / 2)

    def test_source_rows_keep_plus_minus_janus_signs(self) -> None:
        rows = " ".join(row["source_row"] for row in build_payload()["source_rows"])

        self.assertIn("chi(T0i_plus", rows)
        self.assertIn("-chi(B_4vol_minus_from_plus", rows)
        self.assertIn("T0i_minus_to_plus", rows)
        self.assertIn("T0i_plus_to_minus", rows)

    def test_operator_closed_but_matter_transport_open(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "g0i-shift-operator-derived-matter-open")
        self.assertTrue(payload["g0i_operator_derived"])
        self.assertTrue(payload["shift_poisson_operator_transverse_closed"])
        self.assertTrue(payload["psi_time_derivative_retained"])
        self.assertFalse(payload["t0i_source_transport_closed"])
        self.assertFalse(payload["pressure_pi0i_transport_closed"])
        self.assertFalse(payload["source_derived_beta_available"])
        self.assertFalse(payload["prediction_ready"])

    def test_no_fit_or_physics_closure(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])

    def test_markdown_reports_open_matter_transport(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("T0i source transport closed: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
