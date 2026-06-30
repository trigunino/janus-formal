from __future__ import annotations

import unittest

import numpy as np

from scripts.build_p0_weakfield_curvature_injection_probe import (
    build_curvature_injection_system,
    build_payload,
    build_reference_metric_potentials,
    build_two_potential_curvature_injection_system,
    inject_curl_defect,
)


class P0WeakfieldCurvatureInjectionProbeTests(unittest.TestCase):
    def test_probe_is_bounded_not_predictive(self) -> None:
        payload = build_payload()

        self.assertEqual(payload["status"], "bounded-numeric-curvature-injection-probe")
        self.assertEqual(
            payload["source_chain_artifact"],
            "p0_janus_weakfield_delta_phi_psi_source_chain_gate",
        )
        self.assertTrue(payload["source_chain_delta_psi_row_derived"])
        self.assertFalse(payload["source_chain_general_slip_closed"])
        self.assertIn("scipy.linalg.lstsq via solve_linear_probe", payload["tooling"])
        self.assertEqual(payload["potential_source"], "Phi_minus-Phi_plus")
        self.assertEqual(payload["metric_potential_sources"], ["Delta_Phi", "Delta_Psi"])
        self.assertFalse(payload["uses_observational_fit"])
        self.assertFalse(payload["uses_posthoc_qcross"])
        self.assertFalse(payload["uses_scalar_absorption"])
        self.assertFalse(payload["physics_closed"])
        self.assertFalse(payload["prediction_ready"])

    def test_integrable_rows_and_curl_defect_are_distinguished(self) -> None:
        payload = build_payload()

        self.assertTrue(payload["integrable_case_closes"])
        self.assertTrue(payload["two_potential_case_closes"])
        self.assertFalse(payload["curl_defected_case_closes"])
        self.assertLess(payload["integrable_probe"]["residual_norm"], 1e-10)
        self.assertLess(payload["two_potential_probe"]["residual_norm"], 1e-10)
        self.assertGreater(payload["curl_defected_probe"]["residual_norm"], 1e-3)
        self.assertEqual(payload["curl_defect"]["component"], "dxy")
        self.assertEqual(payload["curl_defect"]["defect_type"], "discrete-curl-mixed-derivative-row")

    def test_curvature_rows_match_quadratic_finite_differences(self) -> None:
        yy, xx = np.meshgrid(np.arange(3, dtype=float), np.arange(3, dtype=float), indexing="ij")
        phi_plus = np.zeros((3, 3), dtype=float)
        phi_minus = xx**2 + 2.0 * yy**2 + 3.0 * xx * yy

        matrix, rhs, rows = build_curvature_injection_system(phi_minus, phi_plus)

        self.assertEqual(matrix.shape, (4, 9))
        self.assertEqual([row["component"] for row in rows], ["dxx", "dxy", "dyy", "laplacian"])
        self.assertEqual(rhs.tolist(), [2.0, 3.0, 4.0, 6.0])

    def test_two_potential_system_keeps_phi_and_psi_blocks_separate(self) -> None:
        phi_plus, phi_minus, psi_plus, psi_minus = build_reference_metric_potentials()

        matrix, rhs, rows = build_two_potential_curvature_injection_system(
            phi_minus,
            phi_plus,
            psi_minus,
            psi_plus,
        )

        self.assertEqual(matrix.shape, (72, 50))
        self.assertEqual(rhs.shape, (72,))
        self.assertEqual({row["source"] for row in rows}, {"Delta_Phi", "Delta_Psi"})
        self.assertEqual({row["weakfield_role"] for row in rows}, {"temporal_tidal", "spatial_tidal"})
        self.assertEqual(rows[0]["source"], "Delta_Phi")
        self.assertEqual(rows[-1]["source"], "Delta_Psi")

    def test_defect_targets_central_mixed_row(self) -> None:
        potential = np.arange(25, dtype=float).reshape(5, 5)
        matrix, rhs, rows = build_curvature_injection_system(potential, np.zeros((5, 5)))

        defected_rhs, defect = inject_curl_defect(rhs, rows, amount=0.5)

        self.assertEqual(matrix.shape, (36, 25))
        self.assertEqual(defect["point"], [2, 2])
        self.assertEqual(defect["component"], "dxy")
        self.assertAlmostEqual(defected_rhs[defect["row_index"]] - rhs[defect["row_index"]], 0.5)


if __name__ == "__main__":
    unittest.main()
