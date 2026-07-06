import math
import unittest

import numpy as np

from src.janus_lab.z2_sigma_normal_connection import (
    validate_and_materialize_normal_connection,
)


def _payload() -> dict:
    lambdas = [1.0, 2.0]
    u_grid = [0.0, 0.5, 1.0]
    basis = []
    derivative = []
    for lam in lambdas:
        basis_lam = []
        derivative_lam = []
        for u in u_grid:
            theta = lam * u
            c = math.cos(theta)
            s = math.sin(theta)
            basis_lam.append([[c, s], [-s, c]])
            derivative_lam.append([[-lam * s, lam * c], [-lam * c, -lam * s]])
        basis.append(basis_lam)
        derivative.append(derivative_lam)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_normal_frame_connection_primitives",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambdas,
        "collar_coordinate_u_grid": u_grid,
        "normal_frame_basis_lambda_u": basis,
        "partial_u_normal_frame_basis_lambda_u": derivative,
        "connection_u_matrix_lambda_u": [
            [[[0.0, 0.0], [0.0, 0.0]] for _ in u_grid] for _ in lambdas
        ],
        "ambient_metric_lambda_u": [
            [[[1.0, 0.0], [0.0, 1.0]] for _ in u_grid] for _ in lambdas
        ],
        "primitive_provenance": {
            "normal_frame_basis_lambda_u": "active_collar_normal_frame",
            "partial_u_normal_frame_basis_lambda_u": "active_collar_frame_derivative",
            "connection_u_matrix_lambda_u": "active_collar_levi_civita_connection",
            "ambient_metric_lambda_u": "active_collar_metric",
        },
    }


class Z2SigmaNormalConnectionTest(unittest.TestCase):
    def test_computes_rotating_frame_connection(self):
        payload = validate_and_materialize_normal_connection(_payload())
        self.assertTrue(payload["normal_connection_ready"])
        omega = np.asarray(payload["normal_connection_omega_perp_lambda_u"])
        self.assertEqual(omega.shape, (2, 3, 2, 2))
        self.assertAlmostEqual(omega[0, 0, 0, 1], -1.0)
        self.assertAlmostEqual(omega[0, 0, 1, 0], 1.0)
        self.assertAlmostEqual(omega[1, 1, 0, 1], -2.0)
        self.assertAlmostEqual(omega[1, 1, 1, 0], 2.0)

    def test_rejects_archived_z4_provenance(self):
        payload = _payload()
        payload["primitive_provenance"]["ambient_metric_lambda_u"] = "archived Z4 metric"
        with self.assertRaisesRegex(ValueError, "Forbidden"):
            validate_and_materialize_normal_connection(payload)


if __name__ == "__main__":
    unittest.main()
