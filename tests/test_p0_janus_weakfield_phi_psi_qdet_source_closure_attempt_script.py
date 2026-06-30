from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_phi_psi_qdet_source_closure_attempt import (
    build_payload,
    delta_b4vol_minus_from_plus,
    delta_b4vol_plus_from_minus,
    render_markdown,
)


class P0JanusWeakfieldPhiPsiQdetSourceClosureAttemptTests(unittest.TestCase):
    def test_linearized_determinant_branches_are_reciprocal(self) -> None:
        self.assertEqual(sp.simplify(delta_b4vol_plus_from_minus() + delta_b4vol_minus_from_plus()), 0)

    def test_source_rows_keep_b4vol_feedback_explicit(self) -> None:
        rows = " ".join(row["effective_source"] + " " + row["potential_row"] for row in build_payload()["source_rows"])

        self.assertIn("rho0_minus_to_plus delta_B_4vol_plus_from_minus", rows)
        self.assertIn("rho0_plus_to_minus delta_B_4vol_minus_from_plus", rows)
        self.assertIn("2 Lap(Psi_plus)", rows)
        self.assertIn("2 Lap(Psi_minus)", rows)

    def test_qdet_options_are_separate_not_absorption(self) -> None:
        payload = build_payload()
        options = {row["name"]: row for row in payload["qdet_options"]}

        self.assertEqual(options["positive_effective_density"]["q_det"], "1")
        self.assertEqual(options["negative_proper_density"]["q_det"], "B_4vol_plus_from_minus")
        self.assertTrue(payload["qdet_convention_options_separated"])
        self.assertFalse(payload["qdet_convention_selected_from_source"])
        self.assertFalse(payload["uses_scalar_absorption"])

    def test_attempt_remains_open_and_no_fit(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "phi-psi-qdet-source-closure-attempt-open")
        self.assertTrue(payload["linearized_b4vol_feedback_written"])
        self.assertFalse(payload["phi_psi_source_equations_closed"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_lists_open_requirements(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("background branch", markdown)
        self.assertIn("Phi/Psi source equations closed: False", markdown)
        self.assertIn("Q_det convention selected from source: False", markdown)


if __name__ == "__main__":
    unittest.main()
