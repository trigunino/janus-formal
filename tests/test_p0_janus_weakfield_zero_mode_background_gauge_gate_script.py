from __future__ import annotations

import unittest

import sympy as sp

from scripts.build_p0_janus_weakfield_zero_mode_background_gauge_gate import (
    build_payload,
    common_mode_kernel_residual,
    render_markdown,
    source_compatibility_expression,
    zero_mode_matrix,
)


class P0JanusWeakfieldZeroModeBackgroundGaugeGateTests(unittest.TestCase):
    def test_common_additive_mode_is_kernel(self) -> None:
        self.assertEqual(common_mode_kernel_residual(), sp.Matrix([0, 0]))

    def test_zero_mode_matrix_has_rank_one_structure(self) -> None:
        matrix = zero_mode_matrix()

        self.assertEqual(matrix.shape, (2, 2))
        self.assertEqual(matrix.det(), 0)
        self.assertIn("rho0_minus_to_plus", sp.sstr(matrix[0, 0]))

    def test_source_compatibility_is_explicit(self) -> None:
        expression = sp.sstr(source_compatibility_expression())

        self.assertIn("S_plus*rho0_plus_to_minus", expression)
        self.assertIn("S_minus*rho0_minus_to_plus", expression)

    def test_payload_forbids_using_zero_mode_as_fit(self) -> None:
        payload = build_payload()
        forbidden = " ".join(payload["not_allowed"])

        self.assertEqual(payload["status"], "zero-mode-background-gauge-gate-open")
        self.assertTrue(payload["zero_mode_kernel_identified"])
        self.assertTrue(payload["source_compatibility_written"])
        self.assertTrue(payload["common_mode_gauge_is_not_physics"])
        self.assertIn("tune lensing amplitude", forbidden)
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_markdown_reports_open_background_branch(self) -> None:
        markdown = render_markdown(build_payload())

        self.assertIn("Source compatibility condition", markdown)
        self.assertIn("Background branch selected: False", markdown)
        self.assertIn("Prediction ready: False", markdown)


if __name__ == "__main__":
    unittest.main()
