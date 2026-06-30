from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_shift_boost_t0i_derivation import (
    ETA,
    boost_vector_from_shift,
    build_payload,
    eta_skew_projection,
    render_markdown,
    weakfield_shift_a_matrix,
)


class P0JanusWeakfieldShiftBoostT0iDerivationTests(unittest.TestCase):
    def test_eta_skew_projection_extracts_shift_boost(self) -> None:
        dbx, dby, dbz = sp.symbols("Delta_Bx Delta_By Delta_Bz")
        projection = eta_skew_projection(weakfield_shift_a_matrix())

        self.assertEqual(projection.T * ETA + ETA * projection, sp.zeros(4))
        self.assertEqual(projection[1, 0], dbx / 2)
        self.assertEqual(projection[2, 0], dby / 2)
        self.assertEqual(projection[3, 0], dbz / 2)

    def test_scalar_diagonal_does_not_enter_boost_vector(self) -> None:
        boost = boost_vector_from_shift()

        self.assertEqual([sp.sstr(item) for item in boost], ["Delta_Bx/2", "Delta_By/2", "Delta_Bz/2"])

    def test_payload_links_boost_to_t0i_source_rows_but_keeps_open(self) -> None:
        payload = build_payload()
        rows = " ".join(row["source_row"] + " " + row["momentum_source"] for row in payload["source_rows"])

        self.assertEqual(payload["status"], "shift-boost-t0i-derivation-open")
        self.assertIn("delta G0i_plus", rows)
        self.assertIn("delta G0i_minus", rows)
        self.assertIn("T0i=(rho+p)", rows)
        self.assertTrue(payload["shift_to_boost_derived"])
        self.assertTrue(payload["t0i_source_rows_written"])
        self.assertTrue(payload["source_operator_for_shift_closed"])
        self.assertFalse(payload["source_derived_beta_available"])
        self.assertFalse(payload["same_l_noncomoving_branch_selected"])

    def test_payload_forbids_fit_and_prediction(self) -> None:
        payload = build_payload()

        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_remaining_physical_task(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Derived boost vector", markdown)
        self.assertIn("Source operator for shift closed: True", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
