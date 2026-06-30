from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_curvature_integrability_sparse_pde_probe import (
    build_gradient_system,
    build_payload,
    discrete_curl_defects,
    solve_sparse_probe,
)


class P0CurvatureIntegrabilitySparsePDEProbeTests(unittest.TestCase):
    def test_probe_is_sparse_only_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "sparse-pde-probe-only")
        self.assertIn("scipy.sparse.linalg.lsqr", payload["tooling"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_posthoc_qcross"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_sparse_probe_distinguishes_integrable_and_curl_defect_rows(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["compatible_case_closes"])
        self.assertFalse(payload["incompatible_case_closes"])
        self.assertTrue(payload["compatible_curl_closed"])
        self.assertFalse(payload["incompatible_curl_closed"])
        self.assertLess(payload["compatible_curl_defect_norm"], 1e-12)
        self.assertGreater(payload["incompatible_curl_defect_norm"], 1e-3)
        self.assertLess(payload["compatible_probe"]["residual_norm"], 1e-10)
        self.assertGreater(payload["incompatible_probe"]["residual_norm"], 1e-3)

    def test_gradient_system_has_edges_plus_gauge_fix(self) -> None:
        potential = np.zeros((2, 2))
        matrix, rhs = build_gradient_system(2, 2, potential)

        self.assertEqual(matrix.shape, (5, 4))
        self.assertEqual(rhs.shape, (5,))

    def test_discrete_curl_detects_loop_defect(self) -> None:
        potential = np.array(
            [
                [0.0, 0.2, 0.5],
                [0.1, 0.4, 0.9],
            ]
        )
        _matrix, compatible_rhs = build_gradient_system(3, 2, potential)
        _matrix, incompatible_rhs = build_gradient_system(3, 2, potential, defect=0.25)

        self.assertTrue(np.allclose(discrete_curl_defects(3, 2, compatible_rhs), 0.0))
        self.assertGreater(np.linalg.norm(discrete_curl_defects(3, 2, incompatible_rhs)), 1e-3)

    def test_solver_closes_exact_tiny_system(self) -> None:
        potential = np.array([[0.0, 1.0]])
        matrix, rhs = build_gradient_system(2, 1, potential)
        result = solve_sparse_probe(matrix, rhs)

        self.assertTrue(result["closed_at_tolerance"])
        self.assertEqual(result["equation_count"], 2)
        self.assertEqual(result["unknown_count"], 2)


if __name__ == "__main__":
    unittest.main()
