from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_bianchi_minimal_curvature_numeric_probe import (
    build_payload,
    flrw_relative_curvature_rhs,
    solve_linear_probe,
)


class P0BianchiMinimalCurvatureNumericProbeTests(unittest.TestCase):
    def test_probe_is_numeric_only_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "numeric-probe-only")
        self.assertIn("scipy.linalg.lstsq", payload["tooling"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_posthoc_qcross"])
        self.assertEqual(payload["source_curvature_data_supplied"], "homogeneous-flrw-symbolic-proxy")
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_compatible_and_incompatible_cases_are_distinguished(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["compatible_case_closes"])
        self.assertFalse(payload["incompatible_case_closes"])
        self.assertLess(payload["compatible_probe"]["residual_norm"], 1e-10)
        self.assertGreater(payload["incompatible_probe"]["residual_norm"], 1e-3)
        self.assertTrue(payload["flrw_source_case_closes"])
        self.assertLess(payload["flrw_source_probe"]["residual_norm"], 1e-10)

    def test_solver_reports_rank_solution_and_singular_values(self) -> None:
        matrix = np.eye(2)
        rhs = np.array([2.0, -1.0])

        result = solve_linear_probe(matrix, rhs)

        self.assertEqual(result["rank"], 2)
        self.assertEqual(result["unknown_count"], 2)
        self.assertEqual(result["equation_count"], 2)
        self.assertEqual(result["solution"], [2.0, -1.0])
        self.assertTrue(result["closed_at_tolerance"])
        self.assertEqual(len(result["singular_values"]), 2)

    def test_flrw_relative_curvature_rhs_matches_formula(self) -> None:
        rhs = flrw_relative_curvature_rhs(
            h_plus=2.0,
            h_minus=3.0,
            dh_plus=5.0,
            dh_minus=7.0,
        )

        self.assertEqual(rhs.tolist(), [7.0, 7.0, 5.0, 5.0])


if __name__ == "__main__":
    unittest.main()
